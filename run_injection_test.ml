
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Pervasives.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type _ _ =
  compareSpec2Type

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h



(** val pred : int -> int **)

let pred = fun n -> Pervasives.max 0 (n-1)

module Coq__1 = struct
 (** val add : int -> int -> int **)let rec add = (+)
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Pervasives.max 0 (n-m)



type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

module type DecidableTypeOrig =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type EqLtLe =
 sig
  type t
 end

module type OrderedType =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module Nat =
 struct
  type t = int

  (** val zero : int **)

  let zero =
    0

  (** val one : int **)

  let one =
    Pervasives.succ 0

  (** val two : int **)

  let two =
    Pervasives.succ (Pervasives.succ 0)

  (** val succ : int -> int **)

  let succ x =
    Pervasives.succ x

  (** val pred : int -> int **)

  let pred n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun u -> u)
      n

  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Pervasives.succ (add p m))
      n

  (** val double : int -> int **)

  let double n =
    add n n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val sub : int -> int -> int **)

  let rec sub n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun l -> sub k l)
        m)
      n

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Pervasives.succ n) m

  (** val compare : int -> int -> comparison **)

  let rec compare = fun n m -> if n=m then Eq else if n<m then Lt else Gt

  (** val max : int -> int -> int **)

  let rec max n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun m' -> Pervasives.succ (max n' m'))
        m)
      n

  (** val min : int -> int -> int **)

  let rec min n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> 0)
        (fun m' -> Pervasives.succ (min n' m'))
        m)
      n

  (** val even : int -> bool **)

  let rec even n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n' -> even n')
        n0)
      n

  (** val odd : int -> bool **)

  let odd n =
    negb (even n)

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Pervasives.succ 0)
      (fun m0 -> mul n (pow n m0))
      m

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (Pervasives.succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div = (/)

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> y)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y

  (** val gcd : int -> int -> int **)

  let rec gcd a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> b)
      (fun a' -> gcd (modulo b (Pervasives.succ a')) (Pervasives.succ a'))
      a

  (** val square : int -> int **)

  let square n =
    mul n n

  (** val sqrt_iter : int -> int -> int -> int -> int **)

  let rec sqrt_iter k p q r =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> p)
      (fun k' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        sqrt_iter k' (Pervasives.succ p) (Pervasives.succ (Pervasives.succ
          q)) (Pervasives.succ (Pervasives.succ q)))
        (fun r' -> sqrt_iter k' p q r')
        r)
      k

  (** val sqrt : int -> int **)

  let sqrt n =
    sqrt_iter n 0 0 0

  (** val log2_iter : int -> int -> int -> int -> int **)

  let rec log2_iter k p q r =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> p)
      (fun k' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        log2_iter k' (Pervasives.succ p) (Pervasives.succ q) q)
        (fun r' -> log2_iter k' p (Pervasives.succ q) r')
        r)
      k

  (** val log2 : int -> int **)

  let log2 n =
    log2_iter (pred n) 0 (Pervasives.succ 0) 0

  (** val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let rec iter n f x =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> x)
      (fun n0 -> f (iter n0 f x))
      n

  (** val div2 : int -> int **)

  let rec div2 = fun n -> n/2

  (** val testbit : int -> int -> bool **)

  let rec testbit a n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> odd a)
      (fun n0 -> testbit (div2 a) n0)
      n

  (** val shiftl : int -> int -> int **)

  let rec shiftl a n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> a)
      (fun n0 -> double (shiftl a n0))
      n

  (** val shiftr : int -> int -> int **)

  let rec shiftr a n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> a)
      (fun n0 -> div2 (shiftr a n0))
      n

  (** val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int **)

  let rec bitwise op0 n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' ->
      add (if op0 (odd a) (odd b) then Pervasives.succ 0 else 0)
        (mul (Pervasives.succ (Pervasives.succ 0))
          (bitwise op0 n' (div2 a) (div2 b))))
      n

  (** val coq_land : int -> int -> int **)

  let coq_land a b =
    bitwise (&&) a a b

  (** val coq_lor : int -> int -> int **)

  let coq_lor a b =
    bitwise (||) (max a b) a b

  (** val ldiff : int -> int -> int **)

  let ldiff a b =
    bitwise (fun b0 b' -> (&&) b0 (negb b')) a a b

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor a b =
    bitwise xorb (max a b) a b

  (** val recursion : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let rec recursion x f n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> x)
      (fun n0 -> f n0 (recursion x f n0))
      n

  (** val leb_spec0 : int -> int -> reflect **)

  let leb_spec0 x y =
    iff_reflect ((<=) x y)

  (** val ltb_spec0 : int -> int -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_OrderTac =
   struct
    module IsTotal =
     struct
     end

    module Tac =
     struct
     end
   end

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)

    let max_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))

    (** val max_case :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : int -> int -> bool **)

    let max_dec n m =
      max_case n m (fun _ _ _ h0 -> h0) true false

    (** val min_case_strong :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)

    let min_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))

    (** val min_case :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : int -> int -> bool **)

    let min_dec n m =
      min_case n m (fun _ _ _ h0 -> h0) true false
   end

  (** val max_case_strong :
      int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val max_case : int -> int -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : int -> int -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val min_case : int -> int -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : int -> int -> bool **)

  let min_dec =
    Private_Dec.min_dec

  module Private_Parity =
   struct
   end

  module Private_NZPow =
   struct
   end

  module Private_NZSqrt =
   struct
   end

  (** val sqrt_up : int -> int **)

  let sqrt_up a =
    match compare 0 a with
    | Lt -> Pervasives.succ (sqrt (pred a))
    | _ -> 0

  (** val log2_up : int -> int **)

  let log2_up a =
    match compare (Pervasives.succ 0) a with
    | Lt -> Pervasives.succ (log2 (pred a))
    | _ -> 0

  module Private_NZDiv =
   struct
   end

  (** val lcm : int -> int -> int **)

  let lcm a b =
    mul a (div b (gcd a b))

  (** val eqb_spec : int -> int -> reflect **)

  let eqb_spec x y =
    iff_reflect ((=) x y)

  (** val b2n : bool -> int **)

  let b2n = function
  | true -> Pervasives.succ 0
  | false -> 0

  (** val setbit : int -> int -> int **)

  let setbit a n =
    coq_lor a (shiftl (Pervasives.succ 0) n)

  (** val clearbit : int -> int -> int **)

  let clearbit a n =
    ldiff a (shiftl (Pervasives.succ 0) n)

  (** val ones : int -> int **)

  let ones n =
    pred (shiftl (Pervasives.succ 0) n)

  (** val lnot : int -> int -> int **)

  let lnot a n =
    coq_lxor a (ones n)
 end

(** val internal_eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2 **)

let internal_eq_rew_r_dep _ _ hC =
  hC

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos =
 struct
  type t = int

  (** val succ : int -> int **)

  let rec succ = Pervasives.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val pred : int -> int **)

  let pred = fun n -> Pervasives.max 1 (n-1)

  (** val pred_N : int -> int **)

  let pred_N x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> ((fun p->2*p) p))
      (fun p -> (pred_double p))
      (fun _ -> 0)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  (** val mask_rect : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1

  (** val mask_rec : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos 1
  | IsPos p -> IsPos ((fun p->1+2*p) p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos ((fun p->2*p) p)
  | x0 -> x0

  (** val double_pred_mask : int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> IsPos ((fun p->2*p) ((fun p->2*p) p)))
      (fun p -> IsPos ((fun p->2*p) (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val pred_mask : mask -> mask **)

  let pred_mask = function
  | IsPos q ->
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun _ -> IsPos (pred q))
       (fun _ -> IsPos (pred q))
       (fun _ -> IsNul)
       q)
  | _ -> IsNeg

  (** val sub_mask : int -> int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask p q))
        (fun q -> succ_double_mask (sub_mask p q))
        (fun _ -> IsPos ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : int -> int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask_carry p q))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val sub : int -> int -> int **)

  let sub = fun n m -> Pervasives.max 1 (n-m)

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

  let rec iter f x n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n

  (** val pow : int -> int -> int **)

  let pow x =
    iter (mul x) 1

  (** val square : int -> int **)

  let rec square p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> (fun p->1+2*p) ((fun p->2*p)
      (add (square p0) p0)))
      (fun p0 -> (fun p->2*p) ((fun p->2*p) (square p0)))
      (fun _ -> 1)
      p

  (** val div2 : int -> int **)

  let div2 p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> p0)
      (fun p0 -> p0)
      (fun _ -> 1)
      p

  (** val div2_up : int -> int **)

  let div2_up p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ p0)
      (fun p0 -> p0)
      (fun _ -> 1)
      p

  (** val size_nat : int -> int **)

  let rec size_nat p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> Pervasives.succ (size_nat p0))
      (fun p0 -> Pervasives.succ (size_nat p0))
      (fun _ -> Pervasives.succ 0)
      p

  (** val size : int -> int **)

  let rec size p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ (size p0))
      (fun p0 -> succ (size p0))
      (fun _ -> 1)
      p

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val min : int -> int -> int **)

  let min = Pervasives.min

  (** val max : int -> int -> int **)

  let max = Pervasives.max

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val sqrtrem_step :
      (int -> int) -> (int -> int) -> (int * mask) -> int * mask **)

  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = (fun p->1+2*p) ((fun p->2*p) s) in
       let r' = g (f r) in
       if leb s' r'
       then (((fun p->1+2*p) s), (sub_mask r' s'))
       else (((fun p->2*p) s), (IsPos r'))
     | _ ->
       (((fun p->2*p) s),
         (sub_mask (g (f 1)) ((fun p->2*p) ((fun p->2*p) 1)))))

  (** val sqrtrem : int -> int * mask **)

  let rec sqrtrem p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->1+2*p) x) (fun x -> (fun p->1+2*p) x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->2*p) x) (fun x -> (fun p->1+2*p) x)
          (sqrtrem p1))
        (fun _ -> (1, (IsPos ((fun p->2*p) 1))))
        p0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->1+2*p) x) (fun x -> (fun p->2*p) x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->2*p) x) (fun x -> (fun p->2*p) x)
          (sqrtrem p1))
        (fun _ -> (1, (IsPos 1)))
        p0)
      (fun _ -> (1, IsNul))
      p

  (** val sqrt : int -> int **)

  let sqrt p =
    fst (sqrtrem p)

  (** val gcdn : int -> int -> int -> int **)

  let rec gcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun b' ->
          match compare a' b' with
          | Eq -> a
          | Lt -> gcdn n0 (sub b' a') a
          | Gt -> gcdn n0 (sub a' b') b)
          (fun b0 -> gcdn n0 a b0)
          (fun _ -> 1)
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ -> gcdn n0 a0 b)
          (fun b0 -> (fun p->2*p) (gcdn n0 a0 b0))
          (fun _ -> 1)
          b)
        (fun _ -> 1)
        a)
      n

  (** val gcd : int -> int -> int **)

  let gcd a b =
    gcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val ggcdn : int -> int -> int -> int * (int * int) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (1, (a, b)))
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun b' ->
          match compare a' b' with
          | Eq -> (a, (1, 1))
          | Lt ->
            let (g, p) = ggcdn n0 (sub b' a') a in
            let (ba, aa) = p in (g, (aa, (add aa ((fun p->2*p) ba))))
          | Gt ->
            let (g, p) = ggcdn n0 (sub a' b') b in
            let (ab, bb) = p in (g, ((add bb ((fun p->2*p) ab)), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a b0 in
          let (aa, bb) = p in (g, (aa, ((fun p->2*p) bb))))
          (fun _ -> (1, (a, 1)))
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ ->
          let (g, p) = ggcdn n0 a0 b in
          let (aa, bb) = p in (g, (((fun p->2*p) aa), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a0 b0 in (((fun p->2*p) g), p))
          (fun _ -> (1, (a, 1)))
          b)
        (fun _ -> (1, (1, b)))
        a)
      n

  (** val ggcd : int -> int -> int * (int * int) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val coq_Nsucc_double : int -> int **)

  let coq_Nsucc_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val coq_Ndouble : int -> int **)

  let coq_Ndouble n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n

  (** val coq_lor : int -> int -> int **)

  let rec coq_lor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun _ -> p)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->2*p) (coq_lor p0 q0))
        (fun _ -> (fun p->1+2*p) p0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> q)
        (fun q0 -> (fun p->1+2*p) q0)
        (fun _ -> q)
        q)
      p

  (** val coq_land : int -> int -> int **)

  let rec coq_land p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 1)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 1)
        (fun _ -> 0)
        (fun _ -> 1)
        q)
      p

  (** val ldiff : int -> int -> int **)

  let rec ldiff p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Nsucc_double (ldiff p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun _ -> p)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 0)
        (fun _ -> 1)
        (fun _ -> 0)
        q)
      p

  (** val coq_lxor : int -> int -> int **)

  let rec coq_lxor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun _ -> ((fun p->1+2*p) p0))
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> ((fun p->2*p) q0))
        (fun q0 -> ((fun p->1+2*p) q0))
        (fun _ -> 0)
        q)
      p

  (** val shiftl_nat : int -> int -> int **)

  let rec shiftl_nat p n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> p)
      (fun n0 -> (fun p->2*p) (shiftl_nat p n0))
      n

  (** val shiftr_nat : int -> int -> int **)

  let rec shiftr_nat p n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> p)
      (fun n0 -> div2 (shiftr_nat p n0))
      n

  (** val shiftl : int -> int -> int **)

  let shiftl p n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> p)
      (fun n0 -> iter (fun x -> (fun p->2*p) x) p n0)
      n

  (** val shiftr : int -> int -> int **)

  let shiftr p n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> p)
      (fun n0 -> iter div2 p n0)
      n

  (** val testbit_nat : int -> int -> bool **)

  let rec testbit_nat p n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> true)
        (fun n' -> testbit_nat p0 n')
        n)
      (fun p0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n' -> testbit_nat p0 n')
        n)
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> true)
        (fun _ -> false)
        n)
      p

  (** val testbit : int -> int -> bool **)

  let rec testbit p n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun n0 -> testbit p0 (pred_N n0))
        n)
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> false)
        (fun n0 -> testbit p0 (pred_N n0))
        n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        n)
      p

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op0 p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op0 a (iter_op op0 p0 (op0 a a)))
      (fun p0 -> iter_op op0 p0 (op0 a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Pervasives.succ 0)

  (** val of_nat : int -> int **)

  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> 1)
        (fun _ -> succ (of_nat x))
        x)
      n

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n

  (** val eq_dec : int -> int -> bool **)

  let rec eq_dec p x0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        x0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p

  (** val peano_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let rec peano_rect a f p =
    let f2 =
      peano_rect (f 1 a) (fun p0 x ->
        f (succ ((fun p->2*p) p0)) (f ((fun p->2*p) p0) x))
    in
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun q -> f ((fun p->2*p) q) (f2 q))
       (fun q -> f2 q)
       (fun _ -> a)
       p)

  (** val peano_rec : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let peano_rec =
    peano_rect

  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of int * coq_PeanoView

  (** val coq_PeanoView_rect :
      'a1 -> (int -> coq_PeanoView -> 'a1 -> 'a1) -> int -> coq_PeanoView ->
      'a1 **)

  let rec coq_PeanoView_rect f f0 _ = function
  | PeanoOne -> f
  | PeanoSucc (p0, p1) -> f0 p0 p1 (coq_PeanoView_rect f f0 p0 p1)

  (** val coq_PeanoView_rec :
      'a1 -> (int -> coq_PeanoView -> 'a1 -> 'a1) -> int -> coq_PeanoView ->
      'a1 **)

  let rec coq_PeanoView_rec f f0 _ = function
  | PeanoOne -> f
  | PeanoSucc (p0, p1) -> f0 p0 p1 (coq_PeanoView_rec f f0 p0 p1)

  (** val peanoView_xO : int -> coq_PeanoView -> coq_PeanoView **)

  let rec peanoView_xO _ = function
  | PeanoOne -> PeanoSucc (1, PeanoOne)
  | PeanoSucc (p, q0) ->
    PeanoSucc ((succ ((fun p->2*p) p)), (PeanoSucc (((fun p->2*p) p),
      (peanoView_xO p q0))))

  (** val peanoView_xI : int -> coq_PeanoView -> coq_PeanoView **)

  let rec peanoView_xI _ = function
  | PeanoOne -> PeanoSucc ((succ 1), (PeanoSucc (1, PeanoOne)))
  | PeanoSucc (p, q0) ->
    PeanoSucc ((succ ((fun p->1+2*p) p)), (PeanoSucc (((fun p->1+2*p) p),
      (peanoView_xI p q0))))

  (** val peanoView : int -> coq_PeanoView **)

  let rec peanoView p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> peanoView_xI p0 (peanoView p0))
      (fun p0 -> peanoView_xO p0 (peanoView p0))
      (fun _ -> PeanoOne)
      p

  (** val coq_PeanoView_iter :
      'a1 -> (int -> 'a1 -> 'a1) -> int -> coq_PeanoView -> 'a1 **)

  let rec coq_PeanoView_iter a f _ = function
  | PeanoOne -> a
  | PeanoSucc (p, q0) -> f p (coq_PeanoView_iter a f p q0)

  (** val eqb_spec : int -> int -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)

  (** val switch_Eq : comparison -> comparison -> comparison **)

  let switch_Eq c = function
  | Eq -> c
  | x -> x

  (** val mask2cmp : mask -> comparison **)

  let mask2cmp = function
  | IsNul -> Eq
  | IsPos _ -> Gt
  | IsNeg -> Lt

  (** val leb_spec0 : int -> int -> reflect **)

  let leb_spec0 x y =
    iff_reflect (leb x y)

  (** val ltb_spec0 : int -> int -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)

    let max_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))

    (** val max_case :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : int -> int -> bool **)

    let max_dec n m =
      max_case n m (fun _ _ _ h0 -> h0) true false

    (** val min_case_strong :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)

    let min_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))

    (** val min_case :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : int -> int -> bool **)

    let min_dec n m =
      min_case n m (fun _ _ _ h0 -> h0) true false
   end

  (** val max_case_strong :
      int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val max_case : int -> int -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : int -> int -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val min_case : int -> int -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : int -> int -> bool **)

  let min_dec =
    Private_Dec.min_dec
 end

module N =
 struct
  type t = int

  (** val zero : int **)

  let zero =
    0

  (** val one : int **)

  let one =
    1

  (** val two : int **)

  let two =
    ((fun p->2*p) 1)

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val double : int -> int **)

  let double n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n

  (** val succ : int -> int **)

  let succ = Pervasives.succ

  (** val pred : int -> int **)

  let pred = fun n -> Pervasives.max 0 (n-1)

  (** val succ_pos : int -> int **)

  let succ_pos n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> Coq_Pos.succ p)
      n

  (** val add : int -> int -> int **)

  let add = (+)

  (** val sub : int -> int -> int **)

  let sub = fun n m -> Pervasives.max 0 (n-m)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val eqb : int -> int -> bool **)

  let rec eqb n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> false)
        (fun q -> Coq_Pos.eqb p q)
        m)
      n

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val min : int -> int -> int **)

  let min = Pervasives.min

  (** val max : int -> int -> int **)

  let max = Pervasives.max

  (** val div2 : int -> int **)

  let div2 n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p -> p)
        (fun p -> p)
        (fun _ -> 0)
        p0)
      n

  (** val even : int -> bool **)

  let even n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> true)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> true)
        (fun _ -> false)
        p)
      n

  (** val odd : int -> bool **)

  let odd n =
    negb (even n)

  (** val pow : int -> int -> int **)

  let pow n p =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> 0)
        (fun q -> (Coq_Pos.pow q p0))
        n)
      p

  (** val square : int -> int **)

  let square n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> (Coq_Pos.square p))
      n

  (** val log2 : int -> int **)

  let log2 n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p -> (Coq_Pos.size p))
        (fun p -> (Coq_Pos.size p))
        (fun _ -> 0)
        p0)
      n

  (** val size : int -> int **)

  let size n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> (Coq_Pos.size p))
      n

  (** val size_nat : int -> int **)

  let size_nat n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> Coq_Pos.size_nat p)
      n

  (** val pos_div_eucl : int -> int -> int * int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> (0, 1))
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ -> (0, 1))
          (fun _ -> (0, 1))
          (fun _ -> (1, 0))
          p)
        b)
      a

  (** val div_eucl : int -> int -> int * int **)

  let div_eucl a b =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> (0, 0))
      (fun na ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> (0, a))
        (fun _ -> pos_div_eucl na b)
        b)
      a

  (** val div : int -> int -> int **)

  let div = fun a b -> if b=0 then 0 else a/b

  (** val modulo : int -> int -> int **)

  let modulo = fun a b -> if b=0 then a else a mod b

  (** val gcd : int -> int -> int **)

  let gcd a b =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> b)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> a)
        (fun q -> (Coq_Pos.gcd p q))
        b)
      a

  (** val ggcd : int -> int -> int * (int * int) **)

  let ggcd a b =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> (b, (0, 1)))
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> (a, (1, 0)))
        (fun q ->
        let (g, p0) = Coq_Pos.ggcd p q in let (aa, bb) = p0 in (g, (aa, bb)))
        b)
      a

  (** val sqrtrem : int -> int * int **)

  let sqrtrem n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> (0, 0))
      (fun p ->
      let (s, m) = Coq_Pos.sqrtrem p in
      (match m with
       | Coq_Pos.IsPos r -> (s, r)
       | _ -> (s, 0)))
      n

  (** val sqrt : int -> int **)

  let sqrt n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> (Coq_Pos.sqrt p))
      n

  (** val coq_lor : int -> int -> int **)

  let coq_lor n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n)
        (fun q -> (Coq_Pos.coq_lor p q))
        m)
      n

  (** val coq_land : int -> int -> int **)

  let coq_land n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> 0)
        (fun q -> Coq_Pos.coq_land p q)
        m)
      n

  (** val ldiff : int -> int -> int **)

  let rec ldiff n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n)
        (fun q -> Coq_Pos.ldiff p q)
        m)
      n

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n)
        (fun q -> Coq_Pos.coq_lxor p q)
        m)
      n

  (** val shiftl_nat : int -> int -> int **)

  let rec shiftl_nat a n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> a)
      (fun n0 -> double (shiftl_nat a n0))
      n

  (** val shiftr_nat : int -> int -> int **)

  let rec shiftr_nat a n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> a)
      (fun n0 -> div2 (shiftr_nat a n0))
      n

  (** val shiftl : int -> int -> int **)

  let shiftl a n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun a0 -> (Coq_Pos.shiftl a0 n))
      a

  (** val shiftr : int -> int -> int **)

  let shiftr a n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> a)
      (fun p -> Coq_Pos.iter div2 a p)
      n

  (** val testbit_nat : int -> int -> bool **)

  let testbit_nat a =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ _ -> false)
      (fun p -> Coq_Pos.testbit_nat p)
      a

  (** val testbit : int -> int -> bool **)

  let testbit a n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> false)
      (fun p -> Coq_Pos.testbit p n)
      a

  (** val to_nat : int -> int **)

  let to_nat a =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> Coq_Pos.to_nat p)
      a

  (** val of_nat : int -> int **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' -> (Coq_Pos.of_succ_nat n'))
      n

  (** val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n f x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> x)
      (fun p -> Coq_Pos.iter f x p)
      n

  (** val eq_dec : int -> int -> bool **)

  let eq_dec n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun x ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> false)
        (fun p0 -> Coq_Pos.eq_dec x p0)
        m)
      n

  (** val discr : int -> int option **)

  let discr n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> None)
      (fun p -> Some p)
      n

  (** val binary_rect :
      'a1 -> (int -> 'a1 -> 'a1) -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let binary_rect f0 f2 fS2 n =
    let f2' = fun p -> f2 p in
    let fS2' = fun p -> fS2 p in
    ((fun f0 fp n -> if n=0 then f0 () else fp n)
       (fun _ -> f0)
       (fun p ->
       let rec f p0 =
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun p1 -> fS2' p1 (f p1))
           (fun p1 -> f2' p1 (f p1))
           (fun _ -> fS2 0 f0)
           p0
       in f p)
       n)

  (** val binary_rec :
      'a1 -> (int -> 'a1 -> 'a1) -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let binary_rec =
    binary_rect

  (** val peano_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let peano_rect f0 f n =
    let f' = fun p -> f p in
    ((fun f0 fp n -> if n=0 then f0 () else fp n)
       (fun _ -> f0)
       (fun p -> Coq_Pos.peano_rect (f 0 f0) f' p)
       n)

  (** val peano_rec : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let peano_rec =
    peano_rect

  (** val recursion : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let recursion =
    peano_rect

  (** val leb_spec0 : int -> int -> reflect **)

  let leb_spec0 x y =
    iff_reflect (leb x y)

  (** val ltb_spec0 : int -> int -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_OrderTac =
   struct
    module IsTotal =
     struct
     end

    module Tac =
     struct
     end
   end

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)

    let max_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))

    (** val max_case :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : int -> int -> bool **)

    let max_dec n m =
      max_case n m (fun _ _ _ h0 -> h0) true false

    (** val min_case_strong :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)

    let min_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))

    (** val min_case :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : int -> int -> bool **)

    let min_dec n m =
      min_case n m (fun _ _ _ h0 -> h0) true false
   end

  (** val max_case_strong :
      int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val max_case : int -> int -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : int -> int -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val min_case : int -> int -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : int -> int -> bool **)

  let min_dec =
    Private_Dec.min_dec

  module Private_NZPow =
   struct
   end

  module Private_NZSqrt =
   struct
   end

  (** val sqrt_up : int -> int **)

  let sqrt_up a =
    match compare 0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> 0

  (** val log2_up : int -> int **)

  let log2_up a =
    match compare 1 a with
    | Lt -> succ (log2 (pred a))
    | _ -> 0

  module Private_NZDiv =
   struct
   end

  (** val lcm : int -> int -> int **)

  let lcm a b =
    mul a (div b (gcd a b))

  (** val eqb_spec : int -> int -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)

  (** val b2n : bool -> int **)

  let b2n = function
  | true -> 1
  | false -> 0

  (** val setbit : int -> int -> int **)

  let setbit a n =
    coq_lor a (shiftl 1 n)

  (** val clearbit : int -> int -> int **)

  let clearbit a n =
    ldiff a (shiftl 1 n)

  (** val ones : int -> int **)

  let ones n =
    pred (shiftl 1 n)

  (** val lnot : int -> int -> int **)

  let lnot a n =
    coq_lxor a (ones n)
 end

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y :: l0 -> let s = h y a in if s then true else in_dec h a l0

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> default
              | x :: _ -> x)
    (fun m -> match l with
              | [] -> default
              | _ :: t1 -> nth m t1 default)
    n

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> None
              | x :: _ -> Some x)
    (fun n0 -> match l with
               | [] -> None
               | _ :: l0 -> nth_error l0 n0)
    n

(** val remove : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec remove eq_dec0 x = function
| [] -> []
| y :: tl ->
  if eq_dec0 x y then remove eq_dec0 x tl else y :: (remove eq_dec0 x tl)

(** val count_occ : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 -> int **)

let rec count_occ eq_dec0 l x =
  match l with
  | [] -> 0
  | y :: tl ->
    let n = count_occ eq_dec0 tl x in
    if eq_dec0 y x then Pervasives.succ n else n

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x :: l0 -> app x (concat l0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t1 -> (f a) :: (map f t1)

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: t1 -> app (f x) (flat_map f t1)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t1 -> fold_left f t1 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t1 -> f b (fold_right f a0 t1)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| [] -> None
| x :: tl -> if f x then Some x else find f tl

(** val split : ('a1 * 'a2) list -> 'a1 list * 'a2 list **)

let rec split = function
| [] -> ([], [])
| p :: tl ->
  let (x, y) = p in
  let (left, right) = split tl in ((x :: left), (y :: right))

(** val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x :: tl ->
    (match l' with
     | [] -> []
     | y :: tl' -> (x, y) :: (combine tl tl'))

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n0 -> match l with
               | [] -> []
               | a :: l0 -> a :: (firstn n0 l0))
    n

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n0 -> match l with
               | [] -> []
               | _ :: l0 -> skipn n0 l0)
    n

(** val nodup : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec nodup decA = function
| [] -> []
| x :: xs -> if in_dec decA x xs then nodup decA xs else x :: (nodup decA xs)

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start :: (seq (Pervasives.succ start) len0))
    len

(** val repeat : 'a1 -> int -> 'a1 list **)

let rec repeat x n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun k -> x :: (repeat x k))
    n

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Coq_Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Coq_Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Coq_Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Coq_Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : int -> int -> bool **)

  let rec eqb x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q -> Coq_Pos.eqb p q)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q -> Coq_Pos.eqb p q)
        y)
      x

  (** val max : int -> int -> int **)

  let max = Pervasives.max

  (** val to_nat : int -> int **)

  let to_nat z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> Coq_Pos.to_nat p)
      (fun _ -> 0)
      z

  (** val to_N : int -> int **)

  let to_N z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> p)
      (fun _ -> 0)
      z

  (** val of_nat : int -> int **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n0 -> (Coq_Pos.of_succ_nat n0))
      n

  (** val of_N : int -> int **)

  let of_N = fun p -> p

  (** val div2 : int -> int **)

  let div2 z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> (Coq_Pos.div2 p))
        (fun _ -> (Coq_Pos.div2 p))
        (fun _ -> 0)
        p)
      (fun p -> (~-) (Coq_Pos.div2_up p))
      z

  (** val shiftl : int -> int -> int **)

  let shiftl a n =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> a)
      (fun p -> Coq_Pos.iter (mul ((fun p->2*p) 1)) a p)
      (fun p -> Coq_Pos.iter div2 a p)
      n

  (** val coq_lor : int -> int -> int **)

  let coq_lor a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (Coq_Pos.coq_lor a0 b0))
        (fun b0 -> (~-) (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) a0)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (~-)
        (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) b0)))
        (fun b0 -> (~-)
        (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
        b)
      a

  (** val coq_land : int -> int -> int **)

  let coq_land a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> 0)
        (fun b0 -> of_N (Coq_Pos.coq_land a0 b0))
        (fun b0 -> of_N (N.ldiff a0 (Coq_Pos.pred_N b0)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> 0)
        (fun b0 -> of_N (N.ldiff b0 (Coq_Pos.pred_N a0)))
        (fun b0 -> (~-)
        (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
        b)
      a

  (** val eq_dec : int -> int -> bool **)

  let eq_dec x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun x0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun p0 -> Coq_Pos.eq_dec x0 p0)
        (fun _ -> false)
        y)
      (fun x0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun p0 -> Coq_Pos.eq_dec x0 p0)
        y)
      x
 end

(** val zeq_bool : int -> int -> bool **)

let zeq_bool x y =
  match Z.compare x y with
  | Eq -> true
  | _ -> false

(** val n_of_digits : bool list -> int **)

let rec n_of_digits = function
| [] -> 0
| b :: l' ->
  N.add (if b then 1 else 0) (N.mul ((fun p->2*p) 1) (n_of_digits l'))

(** val n_of_ascii : char -> int **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val string_dec : char list -> char list -> bool **)

let rec string_dec s x =
  match s with
  | [] -> (match x with
           | [] -> true
           | _::_ -> false)
  | a::s0 ->
    (match x with
     | [] -> false
     | a0::s1 -> if (=) a a0 then string_dec s0 s1 else false)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val locked_with : unit -> 'a1 -> 'a1 **)

let locked_with _ x0 =
  x0

module Option =
 struct
  (** val apply : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2 **)

  let apply f x = function
  | Some y -> f y
  | None -> x

  (** val bind : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option **)

  let bind f =
    apply f None

  (** val map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

  let map f =
    bind (fun x -> Some (f x))
 end

type ('aT, 'rT) simpl_fun = ('aT, 'rT) __simpl_fun Lazy.t
and ('aT, 'rT) __simpl_fun =
| SimplFun of ('aT -> 'rT)

(** val fun_of_simpl : ('a1, 'a2) simpl_fun -> 'a1 -> 'a2 **)

let fun_of_simpl f x =
  let SimplFun lam = Lazy.force f in lam x

(** val funcomp : unit -> ('a2 -> 'a1) -> ('a3 -> 'a2) -> 'a3 -> 'a1 **)

let funcomp _ f g x =
  f (g x)

(** val addb : bool -> bool -> bool **)

let addb = function
| true -> negb
| false -> (fun x -> x)

(** val isSome : 'a1 option -> bool **)

let isSome = function
| Some _ -> true
| None -> false

(** val is_left : bool -> bool **)

let is_left = function
| true -> true
| false -> false

(** val iffP : bool -> reflect -> reflect **)

let iffP _ pb =
  let _evar_0_ = fun _ _ _ -> ReflectT in
  let _evar_0_0 = fun _ _ _ -> ReflectF in
  (match pb with
   | ReflectT -> _evar_0_ __ __ __
   | ReflectF -> _evar_0_0 __ __ __)

(** val idP : bool -> reflect **)

let idP = function
| true -> ReflectT
| false -> ReflectF

(** val andP : bool -> bool -> reflect **)

let andP b1 b2 =
  if b1 then if b2 then ReflectT else ReflectF else ReflectF

type 't pred0 = 't -> bool

type 't rel = 't -> 't pred0

type 't simpl_pred = ('t, bool) simpl_fun

(** val simplPred : 'a1 pred0 -> 'a1 simpl_pred **)

let simplPred p =
  lazy (SimplFun p)

(** val pred_of_simpl : 'a1 simpl_pred -> 'a1 pred0 **)

let pred_of_simpl =
  fun_of_simpl

type 't simpl_rel = ('t, 't pred0) simpl_fun

(** val simplRel : 'a1 rel -> 'a1 simpl_rel **)

let simplRel r =
  lazy (SimplFun r)

(** val rel_of_simpl_rel : 'a1 simpl_rel -> 'a1 rel **)

let rel_of_simpl_rel =
  fun_of_simpl

type 't mem_pred = 't __mem_pred Lazy.t
and 't __mem_pred =
| Mem of 't pred0

type 't predType = { topred : (__ -> 't pred0);
                     predType__1 : (__ -> 't mem_pred) }

type 't pred_sort = __

(** val mkPredType : ('a2 -> 'a1 -> bool) -> 'a1 predType **)

let mkPredType toP =
  { topred = (Obj.magic toP); predType__1 = (fun p -> lazy (Mem (fun x ->
    Obj.magic toP p x))) }

(** val pred_of_mem : 'a1 mem_pred -> 'a1 pred_sort **)

let pred_of_mem mp =
  let Mem p = Lazy.force mp in Obj.magic p

(** val mem : 'a1 predType -> 'a1 pred_sort -> 'a1 mem_pred **)

let mem pT =
  pT.predType__1

(** val in_mem : 'a1 -> 'a1 mem_pred -> bool **)

let in_mem x mp =
  Obj.magic pred_of_mem mp x

module Equality =
 struct
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  (** val op : 'a1 mixin_of -> 'a1 rel **)

  let op x = x.op

  type coq_type =
    __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort mixin_of **)

  let coq_class cT =
    cT
 end

(** val eq_op : Equality.coq_type -> Equality.sort rel **)

let eq_op t1 =
  (Equality.coq_class t1).Equality.op

(** val eqP : Equality.coq_type -> Equality.sort Equality.axiom **)

let eqP t1 =
  let _evar_0_ = fun _ a -> a in
  let { Equality.op = x; Equality.mixin_of__1 = x0 } = t1 in _evar_0_ x x0

(** val eqb0 : bool -> bool -> bool **)

let eqb0 b =
  addb (negb b)

type 't subType = { val0 : (__ -> 't); sub0 : ('t -> __ -> __);
                    subType__2 : (__ -> ('t -> __ -> __) -> __ -> __) }

type 't sub_sort = __

(** val val0 : 'a1 pred0 -> 'a1 subType -> 'a1 sub_sort -> 'a1 **)

let val0 _ x = x.val0

(** val pair_eq :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
    simpl_rel **)

let pair_eq t1 t2 =
  simplRel (fun u v ->
    (&&) (eq_op t1 (fst u) (fst v)) (eq_op t2 (snd u) (snd v)))

(** val pair_eqP :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
    Equality.axiom **)

let pair_eqP t1 t2 _top_assumption_ =
  let _evar_0_ = fun x1 x2 _top_assumption_0 ->
    let _evar_0_ = fun y1 y2 ->
      iffP ((&&) (eq_op t1 x1 y1) (eq_op t2 x2 y2))
        (andP (eq_op t1 x1 y1) (eq_op t2 x2 y2))
    in
    let (x, x0) = _top_assumption_0 in _evar_0_ x x0
  in
  let (x, x0) = _top_assumption_ in _evar_0_ x x0

(** val prod_eqMixin :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
    Equality.mixin_of **)

let prod_eqMixin t1 t2 =
  { Equality.op = (rel_of_simpl_rel (pair_eq t1 t2)); Equality.mixin_of__1 =
    (pair_eqP t1 t2) }

(** val prod_eqType :
    Equality.coq_type -> Equality.coq_type -> Equality.coq_type **)

let prod_eqType t1 t2 =
  Obj.magic prod_eqMixin t1 t2

(** val tag : ('a1, 'a2) sigT -> 'a1 **)

let tag =
  projT1

(** val tagged : ('a1, 'a2) sigT -> 'a2 **)

let tagged =
  projT2

(** val tagged0 : 'a1 -> 'a2 -> ('a1, 'a2) sigT **)

let tagged0 i x =
  ExistT (i, x)

(** val tagged_as :
    Equality.coq_type -> (Equality.sort, 'a1) sigT -> (Equality.sort, 'a1)
    sigT -> 'a1 **)

let tagged_as i u v =
  match eqP i (tag u) (tag v) with
  | ReflectT -> tagged v
  | ReflectF -> tagged u

(** val tag_eq :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) ->
    (Equality.sort, Equality.sort) sigT -> (Equality.sort, Equality.sort)
    sigT -> bool **)

let tag_eq i t_ u v =
  (&&) (eq_op i (tag u) (tag v))
    (eq_op (t_ (tag u)) (tagged u) (tagged_as i u v))

(** val tag_eqP :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) ->
    (Equality.sort, Equality.sort) sigT Equality.axiom **)

let tag_eqP i t_ _top_assumption_ =
  let _evar_0_ = fun i0 x _top_assumption_0 ->
    let _evar_0_ = fun j ->
      let _evar_0_ = fun y ->
        iffP
          (eq_op (t_ i0) x (tagged_as i (ExistT (i0, x)) (ExistT (i0, y))))
          (eqP (t_ i0) x (tagged_as i (ExistT (i0, x)) (ExistT (i0, y))))
      in
      let _evar_0_0 = fun _ -> ReflectF in
      (match eqP i i0 j with
       | ReflectT -> _evar_0_
       | ReflectF -> _evar_0_0)
    in
    let ExistT (x0, x1) = _top_assumption_0 in _evar_0_ x0 x1
  in
  let ExistT (x, x0) = _top_assumption_ in _evar_0_ x x0

(** val tag_eqMixin :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) ->
    (Equality.sort, Equality.sort) sigT Equality.mixin_of **)

let tag_eqMixin i t_ =
  { Equality.op = (tag_eq i t_); Equality.mixin_of__1 = (tag_eqP i t_) }

(** val tag_eqType :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) ->
    Equality.coq_type **)

let tag_eqType i t_ =
  Obj.magic tag_eqMixin i t_

(** val eqn : int -> int -> bool **)

let rec eqn = (==)

(** val eqnP : int Equality.axiom **)

let eqnP n m =
  iffP (eqn n m) (idP (eqn n m))

(** val nat_eqMixin : int Equality.mixin_of **)

let nat_eqMixin =
  { Equality.op = eqn; Equality.mixin_of__1 = eqnP }

(** val nat_eqType : Equality.coq_type **)

let nat_eqType =
  Obj.magic nat_eqMixin

(** val addn_rec : int -> int -> int **)

let addn_rec =
  add

(** val addn : int -> int -> int **)

let addn =
  addn_rec

(** val subn_rec : int -> int -> int **)

let subn_rec =
  sub

(** val subn : int -> int -> int **)

let subn =
  subn_rec

(** val leq : int -> int -> bool **)

let leq m n =
  eq_op nat_eqType (Obj.magic subn m n) (Obj.magic 0)

(** val minn : int -> int -> int **)

let minn m n =
  if leq (Pervasives.succ m) n then m else n

(** val iter0 : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter0 n f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> x)
    (fun i -> f (iter0 i f x))
    n

(** val muln_rec : int -> int -> int **)

let muln_rec =
  mul

(** val muln : int -> int -> int **)

let muln =
  muln_rec

(** val ncons : int -> 'a1 -> 'a1 list -> 'a1 list **)

let ncons n x =
  iter0 n (fun x0 -> x :: x0)

(** val nseq : int -> 'a1 -> 'a1 list **)

let nseq n x =
  ncons n x []

(** val cat : 'a1 list -> 'a1 list -> 'a1 list **)

let rec cat s1 s2 =
  match s1 with
  | [] -> s2
  | x :: s1' -> x :: (cat s1' s2)

(** val nth0 : 'a1 -> 'a1 list -> int -> 'a1 **)

let rec nth0 x0 s n =
  match s with
  | [] -> x0
  | x :: s' ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> x)
       (fun n' -> nth0 x0 s' n')
       n)

(** val mem_seq :
    Equality.coq_type -> Equality.sort list -> Equality.sort -> bool **)

let rec mem_seq t1 = function
| [] -> (fun _ -> false)
| y :: s' -> let p = mem_seq t1 s' in (fun x -> (||) (eq_op t1 x y) (p x))

type eqseq_class = Equality.sort list

(** val pred_of_eq_seq :
    Equality.coq_type -> eqseq_class -> Equality.sort pred_sort **)

let pred_of_eq_seq t1 s =
  Obj.magic (fun x -> mem_seq t1 s x)

(** val seq_predType : Equality.coq_type -> Equality.sort predType **)

let seq_predType t1 =
  mkPredType (Obj.magic pred_of_eq_seq t1)

(** val undup :
    Equality.coq_type -> Equality.sort list -> Equality.sort list **)

let rec undup t1 = function
| [] -> []
| x :: s' ->
  if in_mem x (mem (seq_predType t1) (Obj.magic s'))
  then undup t1 s'
  else x :: (undup t1 s')

(** val map0 : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map0 f = function
| [] -> []
| x :: s' -> (f x) :: (map0 f s')

(** val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldr f z0 = function
| [] -> z0
| x :: s' -> f x (foldr f z0 s')

(** val foldl : ('a2 -> 'a1 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldl f z = function
| [] -> z
| x :: s' -> foldl f (f z x) s'

(** val unzip1 : ('a1 * 'a2) list -> 'a1 list **)

let unzip1 s =
  map0 fst s

module CodeSeq =
 struct
  (** val decode_rec : int -> int -> int -> int list **)

  let rec decode_rec v q r =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> v :: [])
      (fun q' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> v :: (decode_rec 0 q' q'))
        (fun n ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> decode_rec (Pervasives.succ v) q' q')
          (fun r' -> decode_rec v q' r')
          n)
        r)
      q

  (** val decode : int -> int list **)

  let decode n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> [])
      (fun _ -> decode_rec 0 (pred n) (pred n))
      n
 end

(** val tag_of_pair : ('a1 * 'a2) -> ('a1, 'a2) sigT **)

let tag_of_pair p =
  tagged0 (fst p) (snd p)

(** val pair_of_tag : ('a1, 'a2) sigT -> 'a1 * 'a2 **)

let pair_of_tag u =
  ((tag u), (tagged u))

module Choice =
 struct
  type 't mixin_of =
    't pred0 -> int -> 't option
    (* singleton inductive, whose constructor was Mixin *)

  (** val find : 'a1 mixin_of -> 'a1 pred0 -> int -> 'a1 option **)

  let find m =
    m

  type 't class_of = { base : 't Equality.mixin_of; mixin : 't mixin_of }

  (** val base : 'a1 class_of -> 'a1 Equality.mixin_of **)

  let base x = x.base

  (** val mixin : 'a1 class_of -> 'a1 mixin_of **)

  let mixin x = x.mixin

  type coq_type =
    __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort class_of **)

  let coq_class cT =
    cT

  (** val eqType : coq_type -> Equality.coq_type **)

  let eqType cT =
    (coq_class cT).base

  module InternalTheory =
   struct
    (** val find : coq_type -> sort pred0 -> int -> sort option **)

    let find t1 =
      find (coq_class t1).mixin
   end
 end

(** val pcanChoiceMixin :
    Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort -> 'a1 option) ->
    'a1 Choice.mixin_of **)

let pcanChoiceMixin t1 _ f' =
  let liftP = fun sP -> simplPred (fun x -> Option.apply sP false (f' x)) in
  let sf = fun sP -> lazy (SimplFun (fun n ->
    Option.bind f'
      (Choice.InternalTheory.find t1 (pred_of_simpl (liftP sP)) n)))
  in
  (fun sP -> fun_of_simpl (sf sP))

(** val canChoiceMixin :
    Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort -> 'a1) -> 'a1
    Choice.mixin_of **)

let canChoiceMixin t1 f f' =
  pcanChoiceMixin t1 f (fun y -> Some (f' y))

(** val tagged_choiceMixin :
    Choice.coq_type -> (Choice.sort -> Choice.coq_type) -> (Choice.sort,
    Choice.sort) sigT Choice.mixin_of **)

let tagged_choiceMixin i t_ =
  let ft = fun tP n i0 ->
    Option.map (tagged0 i0)
      (Choice.InternalTheory.find (t_ i0) (funcomp () tP (tagged0 i0)) n)
  in
  let fi = fun tP ni nt ->
    Option.bind (ft tP nt)
      (Choice.InternalTheory.find i (fun i0 -> isSome (ft tP nt i0)) ni)
  in
  (fun tP n ->
  match CodeSeq.decode n with
  | [] -> None
  | ni :: l ->
    (match l with
     | [] -> None
     | nt :: l0 -> (match l0 with
                    | [] -> fi tP ni nt
                    | _ :: _ -> None)))

(** val tagged_choiceType :
    Choice.coq_type -> (Choice.sort -> Choice.coq_type) -> Choice.coq_type **)

let tagged_choiceType i t_ =
  { Choice.base =
    (Equality.coq_class
      (tag_eqType (Choice.eqType i) (fun i0 -> Choice.eqType (t_ i0))));
    Choice.mixin = (Obj.magic tagged_choiceMixin i t_) }

(** val nat_choiceMixin : int Choice.mixin_of **)

let nat_choiceMixin =
  let f = fun p -> lazy (SimplFun (fun n -> if p n then Some n else None)) in
  (fun p -> fun_of_simpl (f p))

(** val nat_choiceType : Choice.coq_type **)

let nat_choiceType =
  { Choice.base = (Equality.coq_class nat_eqType); Choice.mixin =
    (Obj.magic nat_choiceMixin) }

(** val prod_choiceMixin :
    Choice.coq_type -> Choice.coq_type -> (Choice.sort * Choice.sort)
    Choice.mixin_of **)

let prod_choiceMixin t1 t2 =
  canChoiceMixin (tagged_choiceType t1 (fun _ -> t2)) (Obj.magic tag_of_pair)
    (Obj.magic pair_of_tag)

(** val prod_choiceType :
    Choice.coq_type -> Choice.coq_type -> Choice.coq_type **)

let prod_choiceType t1 t2 =
  { Choice.base =
    (Equality.coq_class (prod_eqType (Choice.eqType t1) (Choice.eqType t2)));
    Choice.mixin = (Obj.magic prod_choiceMixin t1 t2) }

module Ord =
 struct
  module Total =
   struct
    type 't mixin_of =
      't rel
      (* singleton inductive, whose constructor was Mixin *)

    (** val leq : 'a1 mixin_of -> 'a1 rel **)

    let leq m =
      m

    type 't class_of = { base : 't Choice.class_of; mixin : 't mixin_of }

    (** val base : 'a1 class_of -> 'a1 Choice.class_of **)

    let base x = x.base

    (** val mixin : 'a1 class_of -> 'a1 mixin_of **)

    let mixin x = x.mixin

    type coq_type =
      __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    (** val coq_class : coq_type -> sort class_of **)

    let coq_class cT =
      cT

    (** val eqType : coq_type -> Equality.coq_type **)

    let eqType cT =
      (coq_class cT).base.Choice.base

    (** val choiceType : coq_type -> Choice.coq_type **)

    let choiceType cT =
      (coq_class cT).base
   end

  (** val leq : Total.coq_type -> Total.sort rel **)

  let leq t1 =
    Total.leq (Total.coq_class t1).Total.mixin

  (** val lt : Total.coq_type -> Total.sort -> Total.sort -> bool **)

  let lt t1 x y =
    (&&) (leq t1 x y) (negb (eq_op (Total.eqType t1) x y))
 end

(** val nat_ordMixin : int Ord.Total.mixin_of **)

let nat_ordMixin =
  leq

(** val nat_ordType : Ord.Total.coq_type **)

let nat_ordType =
  { Ord.Total.base = (Choice.coq_class nat_choiceType); Ord.Total.mixin =
    (Obj.magic nat_ordMixin) }

(** val prod_leq :
    Ord.Total.coq_type -> Ord.Total.coq_type ->
    (Ord.Total.sort * Ord.Total.sort) rel **)

let prod_leq t1 s =
  rel_of_simpl_rel
    (simplRel (fun p1 p2 ->
      if eq_op (Ord.Total.eqType t1) (fst p1) (fst p2)
      then Ord.leq s (snd p1) (snd p2)
      else Ord.leq t1 (fst p1) (fst p2)))

(** val prod_ordMixin :
    Ord.Total.coq_type -> Ord.Total.coq_type ->
    (Ord.Total.sort * Ord.Total.sort) Ord.Total.mixin_of **)

let prod_ordMixin =
  prod_leq

(** val prod_ordType :
    Ord.Total.coq_type -> Ord.Total.coq_type -> Ord.Total.coq_type **)

let prod_ordType t1 s =
  { Ord.Total.base =
    (Choice.coq_class
      (prod_choiceType (Ord.Total.choiceType t1) (Ord.Total.choiceType s)));
    Ord.Total.mixin = (Obj.magic prod_ordMixin t1 s) }

(** val merge :
    Equality.coq_type -> Equality.sort rel -> Equality.sort list ->
    Equality.sort list -> Equality.sort list **)

let rec merge t1 leT s1 = match s1 with
| [] -> (fun x -> x)
| x1 :: s1' ->
  let rec merge_s1 s2 = match s2 with
  | [] -> s1
  | x2 :: s2' ->
    if leT x2 x1 then x2 :: (merge_s1 s2') else x1 :: (merge t1 leT s1' s2)
  in merge_s1

(** val merge_sort_push :
    Equality.coq_type -> Equality.sort rel -> Equality.sort list ->
    Equality.sort list list -> Equality.sort list list **)

let rec merge_sort_push t1 leT s1 ss = match ss with
| [] -> s1 :: ss
| s2 :: ss' ->
  (match s2 with
   | [] -> s1 :: ss'
   | _ :: _ -> [] :: (merge_sort_push t1 leT (merge t1 leT s1 s2) ss'))

(** val merge_sort_pop :
    Equality.coq_type -> Equality.sort rel -> Equality.sort list ->
    Equality.sort list list -> Equality.sort list **)

let rec merge_sort_pop t1 leT s1 = function
| [] -> s1
| s2 :: ss' -> merge_sort_pop t1 leT (merge t1 leT s1 s2) ss'

(** val merge_sort_rec :
    Equality.coq_type -> Equality.sort rel -> Equality.sort list list ->
    Equality.sort list -> Equality.sort list **)

let rec merge_sort_rec t1 leT ss s = match s with
| [] -> merge_sort_pop t1 leT s ss
| x1 :: l ->
  (match l with
   | [] -> merge_sort_pop t1 leT s ss
   | x2 :: s' ->
     let s1 = if leT x1 x2 then x1 :: (x2 :: []) else x2 :: (x1 :: []) in
     merge_sort_rec t1 leT (merge_sort_push t1 leT s1 ss) s')

(** val sort0 :
    Equality.coq_type -> Equality.sort rel -> Equality.sort list ->
    Equality.sort list **)

let sort0 t1 leT =
  merge_sort_rec t1 leT []

(** val divn : int -> int -> int **)

let divn = (/)

(** val modn : int -> int -> int **)

let modn = (fun x y -> x mod y)

(** val dvdn : int -> int -> bool **)

let dvdn d m =
  eq_op nat_eqType (Obj.magic modn m d) (Obj.magic 0)

module FSet =
 struct
  type fset_type = __fset_type Lazy.t
  and __fset_type =
  | FSet of Ord.Total.sort list

  (** val fsval : Ord.Total.coq_type -> fset_type -> Ord.Total.sort list **)

  let fsval _ f =
    let FSet fsval0 = Lazy.force f in fsval0

  type fset_of = fset_type
 end

(** val fset_of_subType :
    Ord.Total.coq_type -> Ord.Total.sort list subType **)

let fset_of_subType t1 =
  { val0 = (Obj.magic FSet.fsval t1); sub0 =
    (Obj.magic (fun x _ -> lazy (FSet.FSet x))); subType__2 = (fun _ k_S u ->
    let FSet.FSet x = Lazy.force (Obj.magic u) in k_S x __) }

(** val fset_key : unit **)

let fset_key =
  ()

(** val fset : Ord.Total.coq_type -> Ord.Total.sort list -> FSet.fset_of **)

let fset t1 =
  locked_with fset_key (fun s ->
    lazy (FSet.FSet (sort0 (Ord.Total.eqType t1) (Ord.leq t1)
                      (undup (Ord.Total.eqType t1) s))))

(** val pred_of_fset :
    Ord.Total.coq_type -> FSet.fset_of -> Ord.Total.sort simpl_pred **)

let pred_of_fset t1 s =
  simplPred (fun x ->
    in_mem x
      (mem (seq_predType (Ord.Total.eqType t1))
        ((Obj.magic fset_of_subType t1).val0 (Obj.magic s))))

(** val fset_predType : Ord.Total.coq_type -> Ord.Total.sort predType **)

let fset_predType t1 =
  mkPredType (fun s -> pred_of_simpl (pred_of_fset t1 s))

(** val fset0 : Ord.Total.coq_type -> FSet.fset_of **)

let fset0 _ =
  lazy (FSet.FSet [])

(** val fset1 : Ord.Total.coq_type -> Ord.Total.sort -> FSet.fset_of **)

let fset1 _ x =
  lazy (FSet.FSet (x :: []))

(** val fsetU :
    Ord.Total.coq_type -> FSet.fset_of -> FSet.fset_of -> FSet.fset_of **)

let fsetU t1 s1 s2 =
  fset t1
    (cat ((fset_of_subType t1).val0 (Obj.magic s1))
      ((fset_of_subType t1).val0 (Obj.magic s2)))

module FMap =
 struct
  type 's fmap_type =
    (Ord.Total.sort * 's) list
    (* singleton inductive, whose constructor was FMap *)

  (** val fmval :
      Ord.Total.coq_type -> 'a1 fmap_type -> (Ord.Total.sort * 'a1) list **)

  let fmval _ f =
    f
 end

(** val fmap :
    Ord.Total.coq_type -> (Ord.Total.sort * 'a1) list -> 'a1 FMap.fmap_type **)

let fmap _ s =
  s

(** val getm_def :
    Ord.Total.coq_type -> (Equality.sort * 'a1) list -> Ord.Total.sort -> 'a1
    option **)

let rec getm_def t1 s k =
  match s with
  | [] -> None
  | p :: s0 ->
    if eq_op (Ord.Total.eqType t1) k (fst p)
    then Some (snd p)
    else getm_def t1 s0 k

(** val getm :
    Ord.Total.coq_type -> 'a1 FMap.fmap_type -> Ord.Total.sort -> 'a1 option **)

let getm t1 m k =
  getm_def t1 (FMap.fmval t1 m) k

(** val setm_def :
    Ord.Total.coq_type -> (Ord.Total.sort * 'a1) list -> Ord.Total.sort ->
    'a1 -> (Ord.Total.sort * 'a1) list **)

let rec setm_def t1 s k v =
  match s with
  | [] -> (k, v) :: []
  | p :: s' ->
    if Ord.lt t1 k (fst p)
    then (k, v) :: s
    else if eq_op (Ord.Total.eqType t1) k (fst p)
         then (k, v) :: s'
         else p :: (setm_def t1 s' k v)

(** val setm :
    Ord.Total.coq_type -> 'a1 FMap.fmap_type -> Ord.Total.sort -> 'a1 -> 'a1
    FMap.fmap_type **)

let setm t1 m k v =
  fmap t1 (setm_def t1 (FMap.fmval t1 m) k v)

(** val mapm :
    Ord.Total.coq_type -> ('a1 -> 'a2) -> 'a1 FMap.fmap_type -> 'a2
    FMap.fmap_type **)

let mapm t1 f m =
  fmap t1 (map0 (fun p -> ((fst p), (f (snd p)))) (FMap.fmval t1 m))

(** val emptym : Ord.Total.coq_type -> 'a1 FMap.fmap_type **)

let emptym t1 =
  fmap t1 []

(** val mkfmap :
    Ord.Total.coq_type -> (Ord.Total.sort * 'a1) list -> 'a1 FMap.fmap_type **)

let mkfmap t1 kvs =
  foldr (fun kv m -> setm t1 m (fst kv) (snd kv)) (emptym t1) kvs

(** val domm : Ord.Total.coq_type -> 'a1 FMap.fmap_type -> FSet.fset_of **)

let domm t1 m =
  fset t1 (unzip1 (FMap.fmval t1 m))

type 't nMap = 't FMap.fmap_type

(** val elementsm : 'a1 nMap -> (int * 'a1) list **)

let elementsm x =
  Obj.magic FMap.fmval nat_ordType x

module Procedure =
 struct
  type id = int

  (** val eqb : id -> id -> bool **)

  let eqb =
    (=)
 end

module Component =
 struct
  type id = int

  type interface = { export : FSet.fset_of; import : FSet.fset_of }

  (** val export : interface -> FSet.fset_of **)

  let export x = x.export

  (** val import : interface -> FSet.fset_of **)

  let import x = x.import

  (** val eqb : id -> id -> bool **)

  let eqb =
    (=)
 end

module Program =
 struct
  type interface = Component.interface nMap
 end

(** val imported_procedure_b :
    Program.interface -> Component.id -> Component.id -> Procedure.id -> bool **)

let imported_procedure_b is c c' p =
  match getm nat_ordType is (Obj.magic c) with
  | Some cI ->
    in_mem (Obj.magic (c', p))
      (mem (fset_predType (prod_ordType nat_ordType nat_ordType))
        (Obj.magic Component.import cI))
  | None -> false

type event =
| ECall of Component.id * Procedure.id * int * Component.id
| ERet of Component.id * int * Component.id

type trace = event list

(** val e0 : trace **)

let e0 =
  []

module Coq_Nat = Nat

module Util =
 struct
  module Z =
   struct
    (** val of_bool : bool -> int **)

    let of_bool = function
    | true -> 1
    | false -> 0
   end
 end

module Block =
 struct
  type id = int

  type offset = int
 end

module Pointer =
 struct
  type t = (Component.id * Block.id) * Block.offset

  (** val component : t -> Component.id **)

  let component = function
  | (p0, _) -> let (c, _) = p0 in c

  (** val block : t -> Block.id **)

  let block = function
  | (p0, _) -> let (_, b) = p0 in b

  (** val offset : t -> Block.offset **)

  let offset = function
  | (_, o) -> o

  (** val eq : t -> t -> bool **)

  let eq p1 p2 =
    let (p, o1) = p1 in
    let (c1, b1) = p in
    let (p0, o2) = p2 in
    let (c2, b2) = p0 in (&&) ((&&) ((=) c1 c2) ((=) b1 b2)) (Z.eqb o1 o2)

  (** val leq : t -> t -> bool option **)

  let leq p1 p2 =
    let (p, o1) = p1 in
    let (c1, b1) = p in
    let (p0, o2) = p2 in
    let (c2, b2) = p0 in
    if (&&) ((=) c1 c2) ((=) b1 b2) then Some (Z.leb o1 o2) else None

  (** val add : t -> int -> t **)

  let add ptr offset0 =
    let (p, o) = ptr in (p, (Z.add o offset0))

  (** val sub : t -> int -> t **)

  let sub ptr offset0 =
    let (p, o) = ptr in (p, (Z.sub o offset0))

  (** val inc : t -> t **)

  let inc ptr =
    add ptr 1
 end

type value =
| Int of int
| Ptr of Pointer.t
| Undef

type binop =
| Add
| Minus
| Mul
| Eq0
| Leq

(** val eval_binop : binop -> value -> value -> value **)

let eval_binop op0 v1 v2 =
  match op0 with
  | Add ->
    (match v1 with
     | Int n ->
       (match v2 with
        | Int n2 -> Int (Z.add n n2)
        | Ptr p -> Ptr (Pointer.add p n)
        | Undef -> Undef)
     | Ptr p -> (match v2 with
                 | Int n -> Ptr (Pointer.add p n)
                 | _ -> Undef)
     | Undef -> Undef)
  | Minus ->
    (match v1 with
     | Int n1 -> (match v2 with
                  | Int n2 -> Int (Z.sub n1 n2)
                  | _ -> Undef)
     | Ptr p ->
       (match v2 with
        | Int n -> Ptr (Pointer.sub p n)
        | Ptr p2 ->
          let (p0, o1) = p in
          let (c1, b1) = p0 in
          let (p1, o2) = p2 in
          let (c2, b2) = p1 in
          if (&&) ((=) c1 c2) ((=) b1 b2) then Int (Z.sub o1 o2) else Undef
        | Undef -> Undef)
     | Undef -> Undef)
  | Mul ->
    (match v1 with
     | Int n1 -> (match v2 with
                  | Int n2 -> Int (Z.mul n1 n2)
                  | _ -> Undef)
     | _ -> Undef)
  | Eq0 ->
    (match v1 with
     | Int n1 ->
       (match v2 with
        | Int n2 -> Int (Util.Z.of_bool (Z.eqb n1 n2))
        | _ -> Undef)
     | Ptr p1 ->
       (match v2 with
        | Ptr p2 -> Int (Util.Z.of_bool (Pointer.eq p1 p2))
        | _ -> Undef)
     | Undef -> Undef)
  | Leq ->
    (match v1 with
     | Int n1 ->
       (match v2 with
        | Int n2 -> Int (Util.Z.of_bool (Z.leb n1 n2))
        | _ -> Undef)
     | Ptr p1 ->
       (match v2 with
        | Ptr p2 ->
          (match Pointer.leq p1 p2 with
           | Some res -> Int (Util.Z.of_bool res)
           | None -> Undef)
        | _ -> Undef)
     | Undef -> Undef)

module type AbstractComponentMemory =
 sig
  type t

  val prealloc : (Block.id * (int, value list) sum) list -> t

  val empty : t

  val reserve_block : t -> t * Block.id

  val alloc : t -> int -> t * Block.id

  val load : t -> Block.id -> Block.offset -> value option

  val store : t -> Block.id -> Block.offset -> value -> t option
 end

module ComponentMemory =
 struct
  type block = value list

  type mem = { content : block nMap; nextblock : Block.id }

  (** val content : mem -> block nMap **)

  let content m =
    m.content

  (** val nextblock : mem -> Block.id **)

  let nextblock m =
    m.nextblock

  type t = mem

  (** val prealloc : (Block.id * (int, value list) sum) list -> t **)

  let prealloc bufs =
    let rec prepare m = function
    | [] -> m
    | y :: bs' ->
      let (b, y0) = y in
      (match y0 with
       | Inl size1 ->
         let chunk = repeat Undef size1 in
         let m' = { content =
           (setm nat_ordType (content m) (Obj.magic b) chunk); nextblock =
           (Nat.max (add (Pervasives.succ 0) b) (nextblock m)) }
         in
         prepare m' bs'
       | Inr chunk ->
         let m' = { content =
           (setm nat_ordType (content m) (Obj.magic b) chunk); nextblock =
           (Nat.max (add (Pervasives.succ 0) b) (nextblock m)) }
         in
         prepare m' bs')
    in prepare { content = (emptym nat_ordType); nextblock = (Pervasives.succ
         0) } bufs

  (** val empty : t **)

  let empty =
    prealloc []

  (** val reserve_block : t -> t * Block.id **)

  let reserve_block m =
    ({ content = (content m); nextblock =
      (add (Pervasives.succ 0) (nextblock m)) }, (nextblock m))

  (** val alloc : mem -> int -> mem * Block.id **)

  let alloc m size1 =
    let fresh_block = nextblock m in
    let chunk = repeat Undef size1 in
    ({ content =
    (setm nat_ordType (content m) (Obj.magic fresh_block) chunk); nextblock =
    (add (Pervasives.succ 0) (nextblock m)) }, fresh_block)

  (** val load : mem -> Block.id -> int -> value option **)

  let load m b i =
    match getm nat_ordType (content m) (Obj.magic b) with
    | Some chunk ->
      ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
         (fun _ -> nth_error chunk (Z.to_nat i))
         (fun _ -> nth_error chunk (Z.to_nat i))
         (fun _ -> None)
         i)
    | None -> None

  (** val block_update : value list -> int -> value -> block option **)

  let rec block_update data offset0 val1 =
    match data with
    | [] -> None
    | val' :: rest ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ -> Some (val1 :: rest))
         (fun offset' ->
         match block_update rest offset' val1 with
         | Some rest' -> Some (val' :: rest')
         | None -> None)
         offset0)

  (** val store : mem -> Block.id -> int -> value -> mem option **)

  let store m b i v =
    match getm nat_ordType (content m) (Obj.magic b) with
    | Some chunk ->
      ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
         (fun _ ->
         match block_update chunk (Z.to_nat i) v with
         | Some chunk' ->
           Some { content =
             (setm nat_ordType (content m) (Obj.magic b) chunk'); nextblock =
             (nextblock m) }
         | None -> None)
         (fun _ ->
         match block_update chunk (Z.to_nat i) v with
         | Some chunk' ->
           Some { content =
             (setm nat_ordType (content m) (Obj.magic b) chunk'); nextblock =
             (nextblock m) }
         | None -> None)
         (fun _ -> None)
         i)
    | None -> None

  (** val load_after_alloc : __ **)

  let load_after_alloc =
    __

  (** val load_after_store : __ **)

  let load_after_store =
    __

  (** val store_after_load : __ **)

  let store_after_load =
    __
 end

module Memory =
 struct
  type t = ComponentMemory.t nMap

  (** val alloc : t -> Component.id -> int -> (t * Pointer.t) option **)

  let alloc mem1 c size1 =
    match getm nat_ordType mem1 (Obj.magic c) with
    | Some memC ->
      let (memC', b) = ComponentMemory.alloc memC size1 in
      Some ((setm nat_ordType mem1 (Obj.magic c) memC'), ((c, b), 0))
    | None -> None

  (** val load : t -> Pointer.t -> value option **)

  let load mem1 ptr =
    match getm nat_ordType mem1 (Obj.magic Pointer.component ptr) with
    | Some memC ->
      ComponentMemory.load memC (Pointer.block ptr) (Pointer.offset ptr)
    | None -> None

  (** val store : t -> Pointer.t -> value -> t option **)

  let store mem1 ptr v =
    match getm nat_ordType mem1 (Obj.magic Pointer.component ptr) with
    | Some memC ->
      (match ComponentMemory.store memC (Pointer.block ptr)
               (Pointer.offset ptr) v with
       | Some memC' ->
         Some (setm nat_ordType mem1 (Obj.magic Pointer.component ptr) memC')
       | None -> None)
    | None -> None
 end

type 'm monad = { ret : (__ -> __ -> 'm);
                  bind0 : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

(** val ret : 'a1 monad -> 'a2 -> 'a1 **)

let ret monad0 x =
  let { ret = ret0; bind0 = _ } = monad0 in Obj.magic ret0 __ x

(** val bind0 : 'a1 monad -> 'a1 -> ('a2 -> 'a1) -> 'a1 **)

let bind0 monad0 x x0 =
  let { ret = _; bind0 = bind1 } = monad0 in Obj.magic bind1 __ __ x x0

(** val option_monad : __ option monad **)

let option_monad =
  { ret = (fun _ x -> Some x); bind0 = (fun _ _ x f ->
    match x with
    | Some y -> f y
    | None -> None) }

type ('s, 'a) sT = 's -> 'a * 's

(** val state_monad : ('a1, __) sT monad **)

let state_monad =
  { ret = (fun _ x s -> (x, s)); bind0 = (fun _ _ s f x ->
    let (x', s') = s x in f x' s') }

type register =
| R_ONE
| R_COM
| R_AUX1
| R_AUX2
| R_RA
| R_SP

type label = int

type imvalue =
| IInt of int
| IPtr of Pointer.t

(** val imm_to_val : imvalue -> value **)

let imm_to_val = function
| IInt n -> Int n
| IPtr p -> Ptr p

type instr =
| INop
| ILabel of label
| IConst of imvalue * register
| IMov of register * register
| IBinOp of binop * register * register * register
| ILoad of register * register
| IStore of register * register
| IAlloc of register * register
| IBnz of register * label
| IJump of register
| IJal of label
| ICall of Component.id * Procedure.id
| IReturn
| IHalt

type code = instr list

module Intermediate =
 struct
  module Register =
   struct
    type t = value nMap

    (** val to_nat : register -> int **)

    let to_nat = function
    | R_ONE -> 0
    | R_COM -> Pervasives.succ 0
    | R_AUX1 -> Pervasives.succ (Pervasives.succ 0)
    | R_AUX2 -> Pervasives.succ (Pervasives.succ (Pervasives.succ 0))
    | R_RA ->
      Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
    | R_SP ->
      Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))))

    (** val init : value FMap.fmap_type **)

    let init =
      mkfmap nat_ordType (((Obj.magic to_nat R_ONE),
        Undef) :: (((Obj.magic to_nat R_COM),
        Undef) :: (((Obj.magic to_nat R_AUX1),
        Undef) :: (((Obj.magic to_nat R_AUX2),
        Undef) :: (((Obj.magic to_nat R_RA),
        Undef) :: (((Obj.magic to_nat R_SP), Undef) :: []))))))

    (** val get : register -> t -> value **)

    let get r regs =
      match getm nat_ordType regs (Obj.magic to_nat r) with
      | Some val1 -> val1
      | None -> Undef

    (** val set : register -> value -> t -> t **)

    let set r val1 regs =
      setm nat_ordType regs (Obj.magic to_nat r) val1

    (** val invalidate : t -> t **)

    let invalidate regs =
      mkfmap nat_ordType (((Obj.magic to_nat R_ONE),
        Undef) :: (((Obj.magic to_nat R_COM),
        (get R_COM regs)) :: (((Obj.magic to_nat R_AUX1),
        Undef) :: (((Obj.magic to_nat R_AUX2),
        Undef) :: (((Obj.magic to_nat R_RA),
        Undef) :: (((Obj.magic to_nat R_SP), Undef) :: []))))))
   end

  module EntryPoint =
   struct
    type t = Block.id nMap nMap

    (** val get : Component.id -> Procedure.id -> t -> Block.id option **)

    let get c p e1 =
      match getm nat_ordType e1 (Obj.magic c) with
      | Some addrs -> getm nat_ordType addrs (Obj.magic p)
      | None -> None
   end

  type program = { prog_interface : Program.interface;
                   prog_procedures : code nMap nMap;
                   prog_buffers : (Block.id * (int, value list) sum) list nMap;
                   prog_main : (Component.id * Procedure.id) option }

  (** val prog_interface : program -> Program.interface **)

  let prog_interface x = x.prog_interface

  (** val prog_procedures : program -> code nMap nMap **)

  let prog_procedures x = x.prog_procedures

  (** val prog_buffers :
      program -> (Block.id * (int, value list) sum) list nMap **)

  let prog_buffers x = x.prog_buffers

  (** val prog_main : program -> (Component.id * Procedure.id) option **)

  let prog_main x = x.prog_main

  (** val alloc_static_buffers :
      program -> ComponentMemory.t FMap.fmap_type -> Ord.Total.sort list ->
      ComponentMemory.t FMap.fmap_type **)

  let rec alloc_static_buffers p mem1 = function
  | [] -> mem1
  | c :: comps' ->
    (match getm nat_ordType p.prog_buffers c with
     | Some cbufs ->
       let mem' = setm nat_ordType mem1 c (ComponentMemory.prealloc cbufs) in
       alloc_static_buffers p mem' comps'
     | None ->
       let mem' = setm nat_ordType mem1 c (ComponentMemory.prealloc []) in
       alloc_static_buffers p mem' comps')

  (** val prepare_initial_memory : program -> Memory.t **)

  let prepare_initial_memory p =
    alloc_static_buffers p (emptym nat_ordType)
      (FSet.fsval nat_ordType (domm nat_ordType p.prog_interface))

  (** val reserve_component_blocks :
      program -> Ord.Total.sort -> ComponentMemory.t -> code nMap -> Block.id
      nMap -> (Ord.Total.sort * code) list -> (ComponentMemory.t * code
      nMap) * Block.id nMap **)

  let rec reserve_component_blocks p c cmem cprocs centrypoints = function
  | [] -> ((cmem, cprocs), centrypoints)
  | y :: procs_code' ->
    let (p0, pcode) = y in
    let (cmem', b) = ComponentMemory.reserve_block cmem in
    let cprocs' = setm nat_ordType cprocs (Obj.magic b) pcode in
    (match getm nat_ordType p.prog_interface c with
     | Some ciface ->
       if in_mem p0
            (mem (fset_predType nat_ordType)
              (Obj.magic Component.export ciface))
       then let centrypoints' = setm nat_ordType centrypoints p0 b in
            reserve_component_blocks p c cmem' cprocs' centrypoints'
              procs_code'
       else reserve_component_blocks p c cmem' cprocs' centrypoints
              procs_code'
     | None ->
       reserve_component_blocks p c cmem' cprocs' centrypoints procs_code')

  (** val reserve_procedures_blocks :
      program -> Memory.t -> code nMap nMap -> EntryPoint.t ->
      (Ord.Total.sort * code nMap) list -> (Memory.t * code nMap
      nMap) * EntryPoint.t **)

  let rec reserve_procedures_blocks p mem1 procs entrypoints = function
  | [] -> ((mem1, procs), entrypoints)
  | y :: comps_code' ->
    let (c, cprocs) = y in
    (match getm nat_ordType mem1 c with
     | Some cmem ->
       let (p0, centrypoints) =
         reserve_component_blocks p c cmem (emptym nat_ordType)
           (emptym nat_ordType) (Obj.magic elementsm cprocs)
       in
       let (cmem', cprocs0) = p0 in
       let mem' = setm nat_ordType mem1 c cmem' in
       let procs' = setm nat_ordType procs c cprocs0 in
       let entrypoints' = setm nat_ordType entrypoints c centrypoints in
       reserve_procedures_blocks p mem' procs' entrypoints' comps_code'
     | None -> reserve_procedures_blocks p mem1 procs entrypoints comps_code')

  (** val prepare_procedures :
      program -> Memory.t -> (Memory.t * code nMap nMap) * EntryPoint.t **)

  let prepare_procedures p mem1 =
    reserve_procedures_blocks p mem1 (emptym nat_ordType)
      (emptym nat_ordType) (Obj.magic elementsm p.prog_procedures)
 end

module type DecidableType =
 DecidableTypeOrig

type 'x compare0 =
| LT
| EQ
| GT

module type Coq_OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module OrderedTypeFacts =
 functor (O:Coq_OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> true
    | _ -> false

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module KeyOrderedType =
 functor (O:Coq_OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module Raw =
 functor (X:Coq_OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  (** val empty : 'a1 t **)

  let empty =
    []

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | [] -> false
  | p :: l ->
    let (k', _) = p in
    (match X.compare k k' with
     | LT -> false
     | EQ -> true
     | GT -> mem k l)

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_mem

  (** val coq_R_mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rect k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rec k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rec k f f0 f1 f2 l _res r0)

  (** val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec mem_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t1, e1) = p in
       let f7 = f6 t1 e1 l __ in
       let f8 = fun _ _ -> let hrec = mem_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t1 e1 l __ in
       let f10 = f4 t1 e1 l __ in
       (match X.compare k t1 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let mem_rec =
    mem_rect

  (** val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem **)

  let coq_R_mem_correct k s _res =
    Obj.magic mem_rect k (fun y _ _ _ -> R_mem_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_mem_3 (y, y0, y1, y2, (mem k y2),
      (y6 (mem k y2) __))) s _res __

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | [] -> None
  | p :: s' ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x
     | GT -> find k s')

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
     * 'elt coq_R_find

  (** val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rect k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s') -> f1 s k' x s' __ __ __
  | R_find_3 (s, k', x, s', _res, r0) ->
    f2 s k' x s' __ __ __ _res r0 (coq_R_find_rect k f f0 f1 f2 s' _res r0)

  (** val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rec k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s') -> f1 s k' x s' __ __ __
  | R_find_3 (s, k', x, s', _res, r0) ->
    f2 s k' x s' __ __ __ _res r0 (coq_R_find_rec k f f0 f1 f2 s' _res r0)

  (** val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec find_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t1, e1) = p in
       let f7 = f6 t1 e1 l __ in
       let f8 = fun _ _ ->
         let hrec = find_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t1 e1 l __ in
       let f10 = f4 t1 e1 l __ in
       (match X.compare k t1 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let find_rec =
    find_rect

  (** val coq_R_find_correct :
      key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find **)

  let coq_R_find_correct k s _res =
    Obj.magic find_rect k (fun y _ _ _ -> R_find_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_find_3 (y, y0, y1, y2, (find k y2),
      (y6 (find k y2) __))) s _res __

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x s = match s with
  | [] -> (k, x) :: []
  | p :: l ->
    let (k', y) = p in
    (match X.compare k k' with
     | LT -> (k, x) :: s
     | EQ -> (k, x) :: l
     | GT -> (k', y) :: (add k x l))

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_add

  (** val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rect k x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rect k x f f0 f1 f2 l _res r0)

  (** val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rec k x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rec k x f f0 f1 f2 l _res r0)

  (** val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec add_rect k x f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t1, e1) = p in
       let f7 = f6 t1 e1 l __ in
       let f8 = fun _ _ ->
         let hrec = add_rect k x f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t1 e1 l __ in
       let f10 = f4 t1 e1 l __ in
       (match X.compare k t1 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let add_rec =
    add_rect

  (** val coq_R_add_correct :
      key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add **)

  let coq_R_add_correct k x s _res =
    add_rect k x (fun y _ _ _ -> R_add_0 y) (fun y y0 y1 y2 _ _ _ _ _ ->
      R_add_1 (y, y0, y1, y2)) (fun y y0 y1 y2 _ _ _ _ _ -> R_add_2 (y, y0,
      y1, y2)) (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_add_3 (y, y0, y1, y2,
      (add k x y2), (y6 (add k x y2) __))) s _res __

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | [] -> []
  | p :: l ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> (k', x) :: (remove k l))

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_remove

  (** val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rect k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l) -> f1 s k' x l __ __ __
  | R_remove_3 (s, k', x, l, _res, r0) ->
    f2 s k' x l __ __ __ _res r0 (coq_R_remove_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rec k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l) -> f1 s k' x l __ __ __
  | R_remove_3 (s, k', x, l, _res, r0) ->
    f2 s k' x l __ __ __ _res r0 (coq_R_remove_rec k f f0 f1 f2 l _res r0)

  (** val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec remove_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t1, e1) = p in
       let f7 = f6 t1 e1 l __ in
       let f8 = fun _ _ ->
         let hrec = remove_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t1 e1 l __ in
       let f10 = f4 t1 e1 l __ in
       (match X.compare k t1 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let remove_rec =
    remove_rect

  (** val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove **)

  let coq_R_remove_correct k s _res =
    Obj.magic remove_rect k (fun y _ _ _ -> R_remove_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_remove_3 (y, y0, y1, y2,
      (remove k y2), (y6 (remove k y2) __))) s _res __

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | [] -> acc
    | p :: m' -> let (k, e1) = p in fold f m' (f k e1 acc)

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
     * ('elt, 'a) coq_R_fold

  (** val coq_R_fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rect f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e1, m', _res, r0) ->
    f1 m acc k e1 m' __ _res r0
      (coq_R_fold_rect f f0 f1 m' (f k e1 acc) _res r0)

  (** val coq_R_fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rec f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e1, m', _res, r0) ->
    f1 m acc k e1 m' __ _res r0
      (coq_R_fold_rec f f0 f1 m' (f k e1 acc) _res r0)

  (** val fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let rec fold_rect f1 f0 f m acc =
    let f2 = f0 m acc in
    let f3 = f m acc in
    (match m with
     | [] -> f2 __
     | p :: l ->
       let (t1, e1) = p in
       let f4 = f3 t1 e1 l __ in
       let hrec = fold_rect f1 f0 f l (f1 t1 e1 acc) in f4 hrec)

  (** val fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let fold_rec =
    fold_rect

  (** val coq_R_fold_correct :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold **)

  let coq_R_fold_correct f m acc _res =
    fold_rect f (fun y y0 _ _ _ -> R_fold_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 _ _ -> R_fold_1 (y, y0, y1, y2, y3,
      (fold f y3 (f y1 y2 y0)), (y5 (fold f y3 (f y1 y2 y0)) __))) m acc _res
      __

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m m' =
    match m with
    | [] -> (match m' with
             | [] -> true
             | _ :: _ -> false)
    | p :: l ->
      let (x, e1) = p in
      (match m' with
       | [] -> false
       | p0 :: l' ->
         let (x', e') = p0 in
         (match X.compare x x' with
          | EQ -> (&&) (cmp e1 e') (equal cmp l l')
          | _ -> false))

  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * X.t compare0
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

  (** val coq_R_equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
      ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
      'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rect cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x, e1, l, x', e', l', _res, r0) ->
    f0 m m' x e1 l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rect cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x, e1, l, x', e', l', _x) ->
    f1 m m' x e1 l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val coq_R_equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
      ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
      'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rec cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x, e1, l, x', e', l', _res, r0) ->
    f0 m m' x e1 l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rec cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x, e1, l, x', e', l', _x) ->
    f1 m m' x e1 l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let rec equal_rect cmp f2 f1 f0 f m m' =
    let f3 = f2 m m' in
    let f4 = f1 m m' in
    let f5 = f0 m m' in
    let f6 = f m m' in
    let f7 = f6 m __ in
    let f8 = f7 m' __ in
    (match m with
     | [] -> let f9 = f3 __ in (match m' with
                                | [] -> f9 __
                                | _ :: _ -> f8 __)
     | p :: l ->
       let (t1, e1) = p in
       let f9 = f5 t1 e1 l __ in
       let f10 = f4 t1 e1 l __ in
       (match m' with
        | [] -> f8 __
        | p0 :: l0 ->
          let (t2, e2) = p0 in
          let f11 = f9 t2 e2 l0 __ in
          let f12 = let _x = X.compare t1 t2 in f11 _x __ in
          let f13 = f10 t2 e2 l0 __ in
          let f14 = fun _ _ ->
            let hrec = equal_rect cmp f2 f1 f0 f l l0 in f13 __ __ hrec
          in
          (match X.compare t1 t2 with
           | EQ -> f14 __ __
           | _ -> f12 __)))

  (** val equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let equal_rec =
    equal_rect

  (** val coq_R_equal_correct :
      ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal **)

  let coq_R_equal_correct cmp m m' _res =
    equal_rect cmp (fun y y0 _ _ _ _ -> R_equal_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 _ _ -> R_equal_1 (y, y0, y1,
      y2, y3, y5, y6, y7, (equal cmp y3 y7), (y11 (equal cmp y3 y7) __)))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ _ _ -> R_equal_2 (y, y0, y1, y2,
      y3, y5, y6, y7, y9)) (fun y y0 y1 _ y3 _ _ _ _ -> R_equal_3 (y, y0, y1,
      y3)) m m' _res __

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | [] -> []
  | p :: m' -> let (k, e1) = p in (k, (f e1)) :: (map f m')

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | [] -> []
  | p :: m' -> let (k, e1) = p in (k, (f k e1)) :: (mapi f m')

  (** val option_cons :
      key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list **)

  let option_cons k o l =
    match o with
    | Some e1 -> (k, e1) :: l
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | [] -> []
  | p :: l -> let (k, e1) = p in option_cons k (f (Some e1) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | [] -> []
  | p :: l' ->
    let (k, e') = p in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | [] -> map2_r f
  | p :: l ->
    let (k, e1) = p in
    let rec map2_aux m' = match m' with
    | [] -> map2_l f m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e1) None) (map2 f l m')
       | EQ -> option_cons k (f (Some e1) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let rec combine m = match m with
  | [] -> map (fun e' -> (None, (Some e')))
  | p :: l ->
    let (k, e1) = p in
    let rec combine_aux m' = match m' with
    | [] -> map (fun e2 -> ((Some e2), None)) m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> (k, ((Some e1), None)) :: (combine l m')
       | EQ -> (k, ((Some e1), (Some e'))) :: (combine l l')
       | GT -> (k', (None, (Some e'))) :: (combine_aux l'))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
      (key * 'a3) list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 []

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (o, o')
    | None -> (match o' with
               | Some _ -> Some (o, o')
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module type Int =
 sig
  type t

  val i2z : t -> int

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int =
 struct
  type t = int

  (** val _0 : int **)

  let _0 =
    0

  (** val _1 : int **)

  let _1 =
    1

  (** val _2 : int **)

  let _2 =
    ((fun p->2*p) 1)

  (** val _3 : int **)

  let _3 =
    ((fun p->1+2*p) 1)

  (** val add : int -> int -> int **)

  let add =
    Z.add

  (** val opp : int -> int **)

  let opp =
    Z.opp

  (** val sub : int -> int -> int **)

  let sub =
    Z.sub

  (** val mul : int -> int -> int **)

  let mul =
    Z.mul

  (** val max : int -> int -> int **)

  let max =
    Z.max

  (** val eqb : int -> int -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : int -> int -> bool **)

  let ltb =
    Z.ltb

  (** val leb : int -> int -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : int -> int -> bool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in if b then true else false

  (** val ge_lt_dec : int -> int -> bool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in if b then false else true

  (** val i2z : t -> int **)

  let i2z n =
    n
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t2, k, e1, t3, t4) ->
    f0 t2 (tree_rect f f0 t2) k e1 t3 (tree_rect f f0 t3) t4

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t2, k, e1, t3, t4) ->
    f0 t2 (tree_rec f f0 t2) k e1 t3 (tree_rec f f0 t3) t4

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h) -> h

  (** val cardinal : 'a1 tree -> int **)

  let rec cardinal = function
  | Leaf -> 0
  | Node (l, _, _, r, _) -> Pervasives.succ (add (cardinal l) (cardinal r))

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _, _) -> false

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x = function
  | Leaf -> false
  | Node (l, y, _, r, _) ->
    (match X.compare x y with
     | LT -> mem x l
     | EQ -> true
     | GT -> mem x r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x = function
  | Leaf -> None
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> find x l
     | EQ -> Some d
     | GT -> find x r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x e1 r =
    Node (l, x, e1, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x d r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.add hr I._2)
    then (match l with
          | Leaf -> assert_false l x d r
          | Node (ll, lx, ld, lr, _) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx ld (create lr x d r)
            else (match lr with
                  | Leaf -> assert_false l x d r
                  | Node (lrl, lrx, lrd, lrr, _) ->
                    create (create ll lx ld lrl) lrx lrd (create lrr x d r)))
    else if I.gt_le_dec hr (I.add hl I._2)
         then (match r with
               | Leaf -> assert_false l x d r
               | Node (rl, rx, rd, rr, _) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x d rl) rx rd rr
                 else (match rl with
                       | Leaf -> assert_false l x d r
                       | Node (rll, rlx, rld, rlr, _) ->
                         create (create l x d rll) rlx rld
                           (create rlr rx rd rr)))
         else create l x d r

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x d = function
  | Leaf -> Node (Leaf, x, d, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | LT -> bal (add x d l) y d' r
     | EQ -> Node (l, y, d, r, h)
     | GT -> bal l y d' (add x d r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1) **)

  let rec remove_min l x d r =
    match l with
    | Leaf -> (r, (x, d))
    | Node (ll, lx, ld, lr, _) ->
      let (l', m) = remove_min ll lx ld lr in ((bal l' x d r), m)

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let (s2', p) = remove_min l2 x2 d2 r2 in
         let (x, d) = p in bal s1 x d s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> bal (remove x l) y d r
     | EQ -> merge l r
     | GT -> bal l y d (remove x r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d ->
      let rec join_aux r = match r with
      | Leaf -> add x d l
      | Node (rl, rx, rd, rr, rh) ->
        if I.gt_le_dec lh (I.add rh I._2)
        then bal ll lx ld (join lr x d r)
        else if I.gt_le_dec rh (I.add lh I._2)
             then bal (join_aux rl) rx rd rr
             else create l x d r
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t1 =
    t1.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t1 =
    t1.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t1 =
    t1.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | EQ -> { t_left = l; t_opt = (Some d); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')

  (** val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d, r, _) -> elements_aux ((x, d) :: (elements_aux acc r)) l

  (** val elements : 'a1 tree -> (key * 'a1) list **)

  let elements m =
    elements_aux [] m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x, d, r, _) -> fold f r (f x d (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect f f0 = function
  | End -> f
  | More (k, e2, t1, e3) -> f0 k e2 t1 e3 (enumeration_rect f f0 e3)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec f f0 = function
  | End -> f
  | More (k, e2, t1, e3) -> f0 k e2 t1 e3 (enumeration_rec f f0 e3)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e1 =
    match m with
    | Leaf -> e1
    | Node (l, x, d, r, _) -> cons l (More (x, d, r, e1))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp x1 d1 cont = function
  | End -> false
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> if cmp d1 d2 then cont (cons r2 e3) else false
     | _ -> false)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, _) ->
      equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> true
  | More (_, _, _, _) -> false

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp m1 m2 =
    equal_cont cmp m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((map f l), x, (f d), (map f r), h)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((mapi f l), x, (f x d), (mapi f r), h)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, _) ->
    (match f x d with
     | Some d' -> join (map_option f l) x d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e1 ->
            join (map2_opt f mapl mapr l1 l2') x1 e1
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d o -> f (Some d) o)
      (map_option (fun _ d -> f (Some d) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem

    (** val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rect x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rec x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find

    (** val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rect x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rec x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

    (** val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rect f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (x, x0, x1, x2) -> f x x0 x1 x2 __ __ __
    | R_bal_1 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_2 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_3 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_4 (x, x0, x1, x2) -> f3 x x0 x1 x2 __ __ __ __ __
    | R_bal_5 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_6 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_7 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_8 (x, x0, x1, x2) -> f7 x x0 x1 x2 __ __ __ __

    (** val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rec f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (x, x0, x1, x2) -> f x x0 x1 x2 __ __ __
    | R_bal_1 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_2 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_3 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_4 (x, x0, x1, x2) -> f3 x x0 x1 x2 __ __ __ __ __
    | R_bal_5 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_6 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_7 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_8 (x, x0, x1, x2) -> f7 x x0 x1 x2 __ __ __ __

    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add

    (** val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rect x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 r0 _res r1)

    (** val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rec x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree * (key * 'elt))
       * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

    (** val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rect f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r0) -> f l x d r0 __
    | R_remove_min_1 (l, x, d, r0, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r0 ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rect f f0 ll lx ld lr _res r1) l' m __

    (** val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rec f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r0) -> f l x d r0 __
    | R_remove_min_1 (l, x, d, r0, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r0 ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rec f f0 ll lx ld lr _res r1) l' m __

    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key * 'elt) * key * 'elt

    (** val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rect f f0 f1 _ _ _ = function
    | R_merge_0 (x, x0) -> f x x0 __
    | R_merge_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
                 x13, x14) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __

    (** val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rec f f0 f1 _ _ _ = function
    | R_merge_0 (x, x0) -> f x x0 __
    | R_merge_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
                 x13, x14) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove

    (** val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rect x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rec x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key * 'elt)

    (** val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rect f f0 f1 _ _ _ = function
    | R_concat_0 (x, x0) -> f x x0 __
    | R_concat_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __

    (** val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rec f f0 f1 _ _ _ = function
    | R_concat_0 (x, x0) -> f x x0 __
    | R_concat_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __

    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree

    (** val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rect x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 r0 _res r1) rl o rr __

    (** val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rec x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 r0 _res r1) rl o rr __

    type ('elt, 'x) coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option

    (** val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rect f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)

    (** val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rec f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)

    type ('elt, 'x0, 'x) coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'x0 tree
    | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
       * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt

    (** val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e1, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e1 __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e1, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e1 __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key * 'a1) list **)

    let rec flatten_e = function
    | End -> []
    | More (x, e2, t1, r) -> (x, e2) :: (app (elements t1) (flatten_e r))
   end
 end

module IntMake =
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty m =
    Raw.is_empty (this m)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add x e1 m =
    Raw.add x e1 (this m)

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove x m =
    Raw.remove x (this m)

  (** val mem : key -> 'a1 t -> bool **)

  let mem x m =
    Raw.mem x (this m)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find x m =
    Raw.find x (this m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Raw.map f (this m)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    Raw.mapi f (this m)

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 f m m' =
    Raw.map2 f (this m) (this m')

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements m =
    Raw.elements (this m)

  (** val cardinal : 'a1 t -> int **)

  let cardinal m =
    Raw.cardinal (this m)

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    Raw.fold f (this m) i

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp m m' =
    Raw.equal cmp (this m) (this m')
 end

module Make =
 functor (X:Coq_OrderedType) ->
 IntMake(Z_as_Int)(X)

module WFacts_fun =
 functor (E:DecidableType) ->
 functor (M:sig
  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end) ->
 struct
  (** val eqb : E.t -> E.t -> bool **)

  let eqb x y =
    if E.eq_dec x y then true else false

  (** val coq_In_dec : 'a1 M.t -> M.key -> bool **)

  let coq_In_dec m x =
    let b = M.mem x m in if b then true else false
 end

module WProperties_fun =
 functor (E:DecidableType) ->
 functor (M:sig
  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end) ->
 struct
  module F = WFacts_fun(E)(M)

  (** val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3 **)

  let uncurry f p =
    f (fst p) (snd p)

  (** val of_list : (M.key * 'a1) list -> 'a1 M.t **)

  let of_list l =
    fold_right (uncurry M.add) M.empty l

  (** val to_list : 'a1 M.t -> (M.key * 'a1) list **)

  let to_list =
    M.elements

  (** val fold_rec :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ ->
      'a3) -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __ ->
      'a3 -> 'a3) -> 'a3 **)

  let fold_rec f i m hempty hstep =
    let f0 = uncurry f in
    let l = rev (M.elements m) in
    let hstep' = fun k e1 a m' m'' x ->
      hstep (fst (k, e1)) (snd (k, e1)) a m' m'' __ __ __ x
    in
    let rec f1 l0 hstep'0 m0 =
      match l0 with
      | [] -> hempty m0 __
      | y :: l1 ->
        let (k, e1) = y in
        hstep'0 k e1 (fold_right f0 i l1) (of_list l1) m0 __ __ __
          (f1 l1 (fun k0 e2 a m' m'' _ _ _ x ->
            hstep'0 k0 e2 a m' m'' __ __ __ x) (of_list l1))
    in f1 l (fun k e1 a m' m'' _ _ _ x -> hstep' k e1 a m' m'' x) m

  (** val fold_rec_bis :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t
      -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t
      -> __ -> __ -> 'a3 -> 'a3) -> 'a3 **)

  let fold_rec_bis f i m pmorphism pempty pstep =
    fold_rec f i m (fun m0 _ -> pmorphism M.empty m0 i __ pempty)
      (fun k e1 a m' m'' _ _ _ x ->
      pmorphism (M.add k e1 m') m'' (f k e1 a) __ (pstep k e1 a m' __ __ x))

  (** val fold_rec_nodep :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key -> 'a1
      -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 **)

  let fold_rec_nodep f i m x x0 =
    fold_rec_bis f i m (fun _ _ _ _ x1 -> x1) x (fun k e1 a _ _ _ x1 ->
      x0 k e1 a __ x1)

  (** val fold_rec_weak :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 -> __
      -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ -> 'a3
      -> 'a3) -> 'a1 M.t -> 'a3 **)

  let fold_rec_weak f i x x0 x1 m =
    fold_rec_bis f i m x x0 (fun k e1 a m' _ _ x2 -> x1 k e1 a m' __ x2)

  (** val fold_rel :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2 ->
      'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 ->
      'a4) -> 'a4 **)

  let fold_rel f g i j m rempty rstep =
    let l = rev (M.elements m) in
    let rstep' = fun k e1 a b x -> rstep k e1 a b __ x in
    let rec f0 l0 rstep'0 =
      match l0 with
      | [] -> rempty
      | y :: l1 ->
        rstep'0 (fst y) (snd y) (fold_right (uncurry f) i l1)
          (fold_right (uncurry g) j l1) __
          (f0 l1 (fun k e1 a0 b _ x -> rstep'0 k e1 a0 b __ x))
    in f0 l (fun k e1 a b _ x -> rstep' k e1 a b x)

  (** val map_induction :
      ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1 ->
      __ -> __ -> 'a2) -> 'a1 M.t -> 'a2 **)

  let map_induction x x0 m =
    fold_rec (fun _ _ _ -> ()) () m x (fun k e1 _ m' m'' _ _ _ x1 ->
      x0 m' m'' x1 k e1 __ __)

  (** val map_induction_bis :
      ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 -> 'a1
      M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2 **)

  let map_induction_bis x x0 x1 m =
    fold_rec_bis (fun _ _ _ -> ()) () m (fun m0 m' _ _ x2 -> x m0 m' __ x2)
      x0 (fun k e1 _ m' _ _ x2 -> x1 k e1 m' __ x2)

  (** val cardinal_inv_2 : 'a1 M.t -> int -> (M.key * 'a1) **)

  let cardinal_inv_2 m _ =
    let l = M.elements m in
    (match l with
     | [] -> assert false (* absurd case *)
     | p :: _ -> p)

  (** val cardinal_inv_2b : 'a1 M.t -> (M.key * 'a1) **)

  let cardinal_inv_2b m =
    let n = M.cardinal m in
    let x = fun x -> cardinal_inv_2 m x in
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> assert false (* absurd case *))
       (fun n0 -> x n0)
       n)

  (** val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t **)

  let filter f m =
    M.fold (fun k e1 m0 -> if f k e1 then M.add k e1 m0 else m0) m M.empty

  (** val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool **)

  let for_all f m =
    M.fold (fun k e1 b -> if f k e1 then b else false) m true

  (** val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool **)

  let exists_ f m =
    M.fold (fun k e1 b -> if f k e1 then true else b) m false

  (** val partition :
      (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t **)

  let partition f m =
    ((filter f m), (filter (fun k e1 -> negb (f k e1)) m))

  (** val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t **)

  let update m1 m2 =
    M.fold M.add m2 m1

  (** val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t **)

  let restrict m1 m2 =
    filter (fun k _ -> M.mem k m2) m1

  (** val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t **)

  let diff m1 m2 =
    filter (fun k _ -> negb (M.mem k m2)) m1

  (** val coq_Partition_In :
      'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool **)

  let coq_Partition_In _ m1 _ k =
    F.coq_In_dec m1 k

  (** val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool **)

  let update_dec _ m' k _ =
    F.coq_In_dec m' k

  (** val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t **)

  let filter_dom f =
    filter (fun k _ -> f k)

  (** val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t **)

  let filter_range f =
    filter (fun _ -> f)

  (** val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool **)

  let for_all_dom f =
    for_all (fun k _ -> f k)

  (** val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool **)

  let for_all_range f =
    for_all (fun _ -> f)

  (** val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool **)

  let exists_dom f =
    exists_ (fun k _ -> f k)

  (** val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool **)

  let exists_range f =
    exists_ (fun _ -> f)

  (** val partition_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t **)

  let partition_dom f =
    partition (fun k _ -> f k)

  (** val partition_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t **)

  let partition_range f =
    partition (fun _ -> f)
 end

module Positive_as_OT = Coq_Pos

module N_as_OT = N

module Backport_OT =
 functor (O:OrderedType) ->
 struct
  type t = O.t

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val compare : O.t -> O.t -> O.t compare0 **)

  let compare x y =
    let c = compSpec2Type x y (O.compare x y) in
    (match c with
     | CompEqT -> EQ
     | CompLtT -> LT
     | CompGtT -> GT)
 end

module Coq_N_as_OT = Backport_OT(N_as_OT)

module BinNatMap = Make(Coq_N_as_OT)

module Coq_backPositive_as_OT = Backport_OT(Positive_as_OT)

module PMap = Make(Coq_backPositive_as_OT)

module PMapExtra = WProperties_fun(Positive_as_OT)(PMap)

module ListUtil =
 struct
  (** val get : int -> 'a1 list -> 'a1 option **)

  let rec get pos l =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> match l with
                | [] -> None
                | x :: _ -> Some x)
      (fun pos' -> match l with
                   | [] -> None
                   | _ :: ls -> get pos' ls)
      pos

  (** val get_by_key :
      ('a1 -> 'a1 -> bool) -> 'a1 -> ('a1 * 'a2) list -> 'a2 option **)

  let rec get_by_key eqb1 k = function
  | [] -> None
  | p :: ls ->
    let (k1, v1) = p in if eqb1 k k1 then Some v1 else get_by_key eqb1 k ls
 end

module RiscMachine =
 struct
  type value = int

  type immediate = int

  type address = int

  type pc = address

  (** val coq_PC0 : pc **)

  let coq_PC0 =
    0

  module Register =
   struct
    type t = int

    (** val coq_R_ONE : t **)

    let coq_R_ONE =
      1

    (** val coq_R_COM : t **)

    let coq_R_COM =
      ((fun p->2*p) 1)

    (** val coq_R_AUX1 : t **)

    let coq_R_AUX1 =
      ((fun p->1+2*p) 1)

    (** val coq_R_AUX2 : t **)

    let coq_R_AUX2 =
      ((fun p->2*p) ((fun p->2*p) 1))

    (** val coq_R_RA : t **)

    let coq_R_RA =
      ((fun p->1+2*p) ((fun p->2*p) 1))

    (** val coq_R_SP : t **)

    let coq_R_SP =
      ((fun p->2*p) ((fun p->1+2*p) 1))

    (** val coq_R_SFI_SP : t **)

    let coq_R_SFI_SP =
      ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))

    (** val coq_R_AND_CODE_MASK : t **)

    let coq_R_AND_CODE_MASK =
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))

    (** val coq_R_AND_DATA_MASK : t **)

    let coq_R_AND_DATA_MASK =
      ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))

    (** val coq_R_OR_CODE_MASK : t **)

    let coq_R_OR_CODE_MASK =
      ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))

    (** val coq_R_OR_DATA_MASK : t **)

    let coq_R_OR_DATA_MASK =
      ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))

    (** val coq_R_T : t **)

    let coq_R_T =
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))

    (** val coq_R_D : t **)

    let coq_R_D =
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        1)))))

    (** val coq_NO_REGISTERS : int **)

    let coq_NO_REGISTERS =
      Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))))))))))))))))))))))))))))))))

    (** val eqb : t -> t -> bool **)

    let eqb =
      N.eqb
   end

  module RegisterFile =
   struct
    type t = value list

    (** val reset_all : t **)

    let reset_all =
      repeat 0 Register.coq_NO_REGISTERS

    (** val update : 'a1 list -> int -> 'a1 -> 'a1 -> 'a1 list **)

    let rec update l pos x def =
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        match l with
        | [] -> x :: []
        | _ :: xs -> x :: xs)
        (fun pos' ->
        match l with
        | [] -> def :: (update l pos' x def)
        | x' :: xs -> x' :: (update xs pos' x def))
        pos

    (** val set_register : Register.t -> value -> t -> t **)

    let set_register reg val1 gen_regs =
      update gen_regs (N.to_nat reg) val1 0

    (** val get_register : Register.t -> t -> value option **)

    let get_register reg gen_regs =
      ListUtil.get (N.to_nat reg) gen_regs
   end

  module ISA =
   struct
    type binop =
    | Addition
    | Subtraction
    | Multiplication
    | Equality
    | Leq
    | BitwiseOr
    | BitwiseAnd
    | ShiftLeft

    type instr =
    | INop
    | IConst of value * Register.t
    | IMov of Register.t * Register.t
    | IBinOp of binop * Register.t * Register.t * Register.t
    | ILoad of Register.t * Register.t
    | IStore of Register.t * Register.t
    | IBnz of Register.t * immediate
    | IJump of Register.t
    | IJal of address
    | IHalt
   end

  type word =
  | Data of value
  | Instruction of ISA.instr

  module Memory =
   struct
    type t = word BinNatMap.t

    (** val get_word : t -> address -> word option **)

    let get_word mem1 ptr =
      BinNatMap.find ptr mem1

    (** val set_value : t -> address -> value -> t **)

    let set_value mem1 ptr val1 =
      BinNatMap.add ptr (Data val1) mem1

    (** val set_instr : t -> address -> ISA.instr -> t **)

    let set_instr mem1 ptr i =
      BinNatMap.add ptr (Instruction i) mem1

    (** val to_address : value -> address **)

    let to_address =
      Z.to_N

    (** val empty : t **)

    let empty =
      BinNatMap.empty
   end

  (** val eval_binop : ISA.binop -> value -> value -> value **)

  let eval_binop op0 op1 op2 =
    match op0 with
    | ISA.Addition -> Z.add op1 op2
    | ISA.Subtraction -> Z.sub op1 op2
    | ISA.Multiplication -> Z.mul op1 op2
    | ISA.Equality -> if zeq_bool op1 op2 then 1 else 0
    | ISA.Leq -> if Z.leb op1 op2 then 1 else 0
    | ISA.BitwiseOr -> Z.coq_lor op1 op2
    | ISA.BitwiseAnd -> Z.coq_land op1 op2
    | ISA.ShiftLeft -> Z.shiftl op1 op2

  (** val inc_pc : pc -> pc **)

  let inc_pc a =
    N.add a 1

  (** val to_value : int -> value **)

  let to_value =
    Z.of_N
 end

module SFIComponent =
 struct
  type id = int
 end

module SFI =
 struct
  (** val coq_OFFSET_BITS_NO : int **)

  let coq_OFFSET_BITS_NO =
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))

  (** val coq_COMP_BITS_NO : int **)

  let coq_COMP_BITS_NO =
    ((fun p->2*p) 1)

  (** val coq_CODE_DATA_BIT_MASK : int **)

  let coq_CODE_DATA_BIT_MASK =
    N.shiftl 1 (N.add coq_OFFSET_BITS_NO coq_COMP_BITS_NO)

  (** val coq_SLOT_SIZE : int **)

  let coq_SLOT_SIZE =
    N.pow ((fun p->2*p) 1) coq_OFFSET_BITS_NO

  (** val coq_COMP_MAX : int **)

  let coq_COMP_MAX =
    N.pow ((fun p->2*p) 1) coq_COMP_BITS_NO

  (** val coq_C_SFI : RiscMachine.address -> SFIComponent.id **)

  let coq_C_SFI addr =
    N.coq_land (N.shiftr addr coq_OFFSET_BITS_NO)
      (N.sub (N.pow ((fun p->2*p) 1) coq_COMP_BITS_NO) 1)

  (** val coq_SLOT_SFI : RiscMachine.address -> int **)

  let coq_SLOT_SFI addr =
    N.shiftr addr (N.add coq_OFFSET_BITS_NO coq_COMP_BITS_NO)

  (** val coq_OFFSET_SFI : RiscMachine.address -> int **)

  let coq_OFFSET_SFI addr =
    N.coq_land addr (N.sub (N.pow ((fun p->2*p) 1) coq_OFFSET_BITS_NO) 1)

  (** val coq_ADDRESS_ALLIGN_BITS_NO : int **)

  let coq_ADDRESS_ALLIGN_BITS_NO =
    ((fun p->2*p) ((fun p->2*p) 1))

  (** val coq_BASIC_BLOCK_SIZE : int **)

  let coq_BASIC_BLOCK_SIZE =
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))

  (** val coq_MONITOR_COMPONENT_ID : int **)

  let coq_MONITOR_COMPONENT_ID =
    0

  (** val coq_BLOCK_BITS_NO : int **)

  let coq_BLOCK_BITS_NO =
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))

  (** val coq_AND_DATA_MASK : int **)

  let coq_AND_DATA_MASK =
    N.coq_lor
      (N.shiftl (N.sub (N.pow ((fun p->2*p) 1) coq_BLOCK_BITS_NO) 1)
        (N.add (N.add coq_OFFSET_BITS_NO coq_COMP_BITS_NO) 1))
      (N.sub (N.pow ((fun p->2*p) 1) coq_OFFSET_BITS_NO) 1)

  (** val coq_AND_CODE_MASK : int **)

  let coq_AND_CODE_MASK =
    N.coq_lor
      (N.shiftl (N.sub (N.pow ((fun p->2*p) 1) coq_BLOCK_BITS_NO) 1)
        (N.add (N.add coq_OFFSET_BITS_NO coq_COMP_BITS_NO) 1))
      (N.shiftl
        (N.sub
          (N.pow ((fun p->2*p) 1)
            (N.sub coq_OFFSET_BITS_NO coq_ADDRESS_ALLIGN_BITS_NO)) 1)
        coq_ADDRESS_ALLIGN_BITS_NO)

  (** val last_address_in_slot : RiscMachine.address -> bool **)

  let last_address_in_slot addr =
    N.eqb (coq_OFFSET_SFI addr)
      (N.sub (N.pow ((fun p->2*p) 1) coq_OFFSET_BITS_NO) 1)

  (** val address_of :
      SFIComponent.id -> int -> int -> RiscMachine.address **)

  let address_of cid bid off =
    N.coq_lor (N.shiftl bid (N.add coq_COMP_BITS_NO coq_OFFSET_BITS_NO))
      (N.coq_lor (N.shiftl cid coq_OFFSET_BITS_NO) off)

  (** val convert_address :
      RiscMachine.address -> (SFIComponent.id * int) * int **)

  let convert_address addr =
    (((coq_C_SFI addr), (coq_SLOT_SFI addr)), (coq_OFFSET_SFI addr))

  (** val is_same_component_bool :
      RiscMachine.address -> RiscMachine.address -> bool **)

  let is_same_component_bool addr1 addr2 =
    N.eqb (coq_C_SFI addr1) (coq_C_SFI addr2)

  (** val is_code_address : RiscMachine.address -> bool **)

  let is_code_address addr =
    N.eqb (N.coq_land addr coq_CODE_DATA_BIT_MASK) 0

  (** val or_data_mask : SFIComponent.id -> int **)

  let or_data_mask cid =
    N.shiftl (N.coq_lor (N.shiftl 1 coq_COMP_BITS_NO) cid) coq_OFFSET_BITS_NO

  (** val or_code_mask : SFIComponent.id -> int **)

  let or_code_mask cid =
    N.shiftl cid coq_OFFSET_BITS_NO

  module Allocator =
   struct
    (** val allocator_data_slot : int **)

    let allocator_data_slot =
      1

    (** val allocate_data_slots : int -> int list **)

    let allocate_data_slots n =
      map (fun nn -> N.add (N.mul ((fun p->2*p) 1) (N.of_nat nn)) 1)
        (seq (Pervasives.succ 0) n)

    (** val allocate_code_slots : int -> int list **)

    let allocate_code_slots n =
      map (fun n0 -> N.mul (N.of_nat n0) ((fun p->2*p) 1)) (seq 0 n)

    (** val initial_allocator_value : int -> RiscMachine.value **)

    let initial_allocator_value =
      Z.of_nat
   end
 end

module Env =
 struct
  type coq_CN = Component.id list

  type coq_E = (RiscMachine.address * Procedure.id) list

  type t = coq_CN * coq_E

  (** val index2SFIid : int -> SFIComponent.id **)

  let index2SFIid i =
    N.add (N.of_nat i) 1

  (** val coq_SFIid2index : SFIComponent.id -> int **)

  let coq_SFIid2index id0 =
    N.to_nat (N.sub id0 1)

  (** val get_component_name_from_id :
      SFIComponent.id -> t -> Component.id option **)

  let get_component_name_from_id id0 g =
    ListUtil.get (coq_SFIid2index id0) (fst g)

  (** val get_procedure : RiscMachine.address -> t -> Procedure.id option **)

  let get_procedure addr g =
    ListUtil.get_by_key N.eqb addr (snd g)
 end

module MachineState =
 struct
  type t =
    (RiscMachine.Memory.t * RiscMachine.pc) * RiscMachine.RegisterFile.t

  (** val getMemory : t -> RiscMachine.Memory.t **)

  let getMemory st =
    fst (fst st)

  (** val getPC : t -> RiscMachine.pc **)

  let getPC st =
    snd (fst st)

  (** val getRegs : t -> RiscMachine.RegisterFile.t **)

  let getRegs =
    snd
 end

type sfi_program = { cn : Env.coq_CN; e : Env.coq_E;
                     mem0 : RiscMachine.Memory.t;
                     prog_interface0 : Program.interface }

(** val cn : sfi_program -> Env.coq_CN **)

let cn x = x.cn

(** val e : sfi_program -> Env.coq_E **)

let e x = x.e

(** val mem0 : sfi_program -> RiscMachine.Memory.t **)

let mem0 x = x.mem0

type label0 = int * int

type ainstr =
| INop0
| ILabel0 of label0
| IConst0 of RiscMachine.value * RiscMachine.Register.t
| IMov0 of RiscMachine.Register.t * RiscMachine.Register.t
| IBinOp0 of RiscMachine.ISA.binop * RiscMachine.Register.t
   * RiscMachine.Register.t * RiscMachine.Register.t
| ILoad0 of RiscMachine.Register.t * RiscMachine.Register.t
| IStore0 of RiscMachine.Register.t * RiscMachine.Register.t
| IBnz0 of RiscMachine.Register.t * label0
| IJump0 of RiscMachine.Register.t
| IJal0 of label0
| IHalt0

type code0 = ainstr list

type lcode = (label0 list option * ainstr) list

(** val map_register : register -> RiscMachine.Register.t **)

let map_register = function
| R_ONE -> RiscMachine.Register.coq_R_ONE
| R_COM -> RiscMachine.Register.coq_R_COM
| R_AUX1 -> RiscMachine.Register.coq_R_AUX1
| R_AUX2 -> RiscMachine.Register.coq_R_AUX2
| R_RA -> RiscMachine.Register.coq_R_RA
| R_SP -> RiscMachine.Register.coq_R_SP

(** val map_binop : binop -> RiscMachine.ISA.binop **)

let map_binop = function
| Add -> RiscMachine.ISA.Addition
| Minus -> RiscMachine.ISA.Subtraction
| Mul -> RiscMachine.ISA.Multiplication
| Eq0 -> RiscMachine.ISA.Equality
| Leq -> RiscMachine.ISA.Leq

(** val label_eqb : label0 -> label0 -> bool **)

let label_eqb l1 l2 =
  let (c1, i1) = l1 in
  let (c2, i2) = l2 in (&&) (Coq_Pos.eqb c1 c2) (N.eqb i1 i2)

(** val label_eq_dec : label0 -> label0 -> bool **)

let label_eq_dec l1 l2 =
  let (x, x0) = l1 in
  let (p, n) = l2 in
  if let rec f p0 x1 =
       (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
         (fun p1 ->
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun p2 -> f p1 p2)
           (fun _ -> false)
           (fun _ -> false)
           x1)
         (fun p1 ->
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun _ -> false)
           (fun p2 -> f p1 p2)
           (fun _ -> false)
           x1)
         (fun _ ->
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun _ -> false)
           (fun _ -> false)
           (fun _ -> true)
           x1)
         p0
     in f x p
  then ((fun f0 fp n -> if n=0 then f0 () else fp n)
          (fun _ ->
          (fun f0 fp n -> if n=0 then f0 () else fp n)
            (fun _ -> true)
            (fun _ -> false)
            n)
          (fun x1 ->
          (fun f0 fp n -> if n=0 then f0 () else fp n)
            (fun _ -> false)
            (fun p1 ->
            let rec f p0 x2 =
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p2 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun p3 -> f p2 p3)
                  (fun _ -> false)
                  (fun _ -> false)
                  x2)
                (fun p2 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> false)
                  (fun p3 -> f p2 p3)
                  (fun _ -> false)
                  x2)
                (fun _ ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> false)
                  (fun _ -> false)
                  (fun _ -> true)
                  x2)
                p0
            in f x1 p1)
            n)
          x0)
  else false

type compilerError =
| NoInfo
| DuplicatedLabels of lcode PMap.t PMap.t
| ExportedProcsLabelsC of int * label0 PMap.t PMap.t
| ExportedProcsLabelsP of int * int * label0 PMap.t PMap.t
| PosArg of int
| TwoPosArg of int * int

type 'a compEither =
| Right of 'a
| Left of char list * compilerError

module CompStateMonad =
 struct
  type ('st, 'res) t = 'st -> 'res compEither * 'st

  (** val ret : 'a2 -> ('a1, 'a2) t **)

  let ret x s =
    ((Right x), s)

  (** val bind :
      ('a1, 'a2) t -> ('a2 -> ('a1, 'a3) t) -> 'a1 -> 'a3 compEither * 'a1 **)

  let bind s f x =
    let (c, s') = s x in
    (match c with
     | Right x' -> f x' s'
     | Left (msg, err) -> ((Left (msg, err)), s'))

  (** val get : ('a1, 'a1) t **)

  let get s =
    ((Right s), s)

  (** val modify : ('a1 -> 'a1) -> ('a1, unit) t **)

  let modify f s =
    ((Right ()), (f s))

  (** val lift : 'a2 option -> char list -> compilerError -> ('a1, 'a2) t **)

  let lift x msg _ s =
    match x with
    | Some v -> ((Right v), s)
    | None -> ((Left (msg, NoInfo)), s)

  (** val fail : char list -> compilerError -> ('a1, 'a2) t **)

  let fail msg err s =
    ((Left (msg, err)), s)

  (** val run : 'a1 -> ('a1, 'a2) t -> 'a2 compEither **)

  let run s m =
    let (c, _) = m s in c
 end

(** val state_monad0 : ('a1, __) CompStateMonad.t monad **)

let state_monad0 =
  { ret = (fun _ -> CompStateMonad.ret); bind0 = (fun _ _ ->
    CompStateMonad.bind) }

type comp_flags = { store_instr_off : bool; store_instr1_off : bool;
                    store_instr2_off : bool; jump_instr_off : bool;
                    jump_instr1_off : bool; jump_instr2_off : bool;
                    push_sfi_halt_not_present : bool;
                    pop_sfi_not_aligned : bool;
                    set_sfi_registers_missing : bool;
                    after_call_label_missing : bool;
                    targets_not_aligned : bool }

(** val store_instr_off : comp_flags -> bool **)

let store_instr_off x = x.store_instr_off

(** val store_instr1_off : comp_flags -> bool **)

let store_instr1_off x = x.store_instr1_off

(** val store_instr2_off : comp_flags -> bool **)

let store_instr2_off x = x.store_instr2_off

(** val jump_instr_off : comp_flags -> bool **)

let jump_instr_off x = x.jump_instr_off

(** val jump_instr1_off : comp_flags -> bool **)

let jump_instr1_off x = x.jump_instr1_off

(** val jump_instr2_off : comp_flags -> bool **)

let jump_instr2_off x = x.jump_instr2_off

(** val push_sfi_halt_not_present : comp_flags -> bool **)

let push_sfi_halt_not_present x = x.push_sfi_halt_not_present

(** val pop_sfi_not_aligned : comp_flags -> bool **)

let pop_sfi_not_aligned x = x.pop_sfi_not_aligned

(** val set_sfi_registers_missing : comp_flags -> bool **)

let set_sfi_registers_missing x = x.set_sfi_registers_missing

(** val after_call_label_missing : comp_flags -> bool **)

let after_call_label_missing x = x.after_call_label_missing

(** val targets_not_aligned : comp_flags -> bool **)

let targets_not_aligned x = x.targets_not_aligned

(** val set_store_instr_off : comp_flags **)

let set_store_instr_off =
  { store_instr_off = true; store_instr1_off = false; store_instr2_off =
    false; jump_instr_off = false; jump_instr1_off = false; jump_instr2_off =
    false; push_sfi_halt_not_present = false; pop_sfi_not_aligned = false;
    set_sfi_registers_missing = false; after_call_label_missing = false;
    targets_not_aligned = false }

(** val set_store_instr1_off : comp_flags **)

let set_store_instr1_off =
  { store_instr_off = false; store_instr1_off = true; store_instr2_off =
    false; jump_instr_off = false; jump_instr1_off = false; jump_instr2_off =
    false; push_sfi_halt_not_present = false; pop_sfi_not_aligned = false;
    set_sfi_registers_missing = false; after_call_label_missing = false;
    targets_not_aligned = false }

(** val set_store_instr2_off : comp_flags **)

let set_store_instr2_off =
  { store_instr_off = false; store_instr1_off = false; store_instr2_off =
    true; jump_instr_off = false; jump_instr1_off = false; jump_instr2_off =
    false; push_sfi_halt_not_present = false; pop_sfi_not_aligned = false;
    set_sfi_registers_missing = false; after_call_label_missing = false;
    targets_not_aligned = false }

(** val set_jump_instr_off : comp_flags **)

let set_jump_instr_off =
  { store_instr_off = false; store_instr1_off = false; store_instr2_off =
    false; jump_instr_off = true; jump_instr1_off = false; jump_instr2_off =
    false; push_sfi_halt_not_present = false; pop_sfi_not_aligned = false;
    set_sfi_registers_missing = false; after_call_label_missing = false;
    targets_not_aligned = false }

(** val set_jump_instr1_off : comp_flags **)

let set_jump_instr1_off =
  { store_instr_off = false; store_instr1_off = false; store_instr2_off =
    false; jump_instr_off = false; jump_instr1_off = true; jump_instr2_off =
    false; push_sfi_halt_not_present = false; pop_sfi_not_aligned = false;
    set_sfi_registers_missing = false; after_call_label_missing = false;
    targets_not_aligned = false }

(** val set_jump_instr2_off : comp_flags **)

let set_jump_instr2_off =
  { store_instr_off = false; store_instr1_off = false; store_instr2_off =
    false; jump_instr_off = false; jump_instr1_off = false; jump_instr2_off =
    true; push_sfi_halt_not_present = false; pop_sfi_not_aligned = false;
    set_sfi_registers_missing = false; after_call_label_missing = false;
    targets_not_aligned = false }

(** val set_push_sfi_halt_not_present : comp_flags **)

let set_push_sfi_halt_not_present =
  { store_instr_off = false; store_instr1_off = false; store_instr2_off =
    false; jump_instr_off = false; jump_instr1_off = false; jump_instr2_off =
    false; push_sfi_halt_not_present = true; pop_sfi_not_aligned = false;
    set_sfi_registers_missing = false; after_call_label_missing = false;
    targets_not_aligned = false }

(** val set_pop_sfi_not_aligned : comp_flags **)

let set_pop_sfi_not_aligned =
  { store_instr_off = false; store_instr1_off = false; store_instr2_off =
    false; jump_instr_off = false; jump_instr1_off = false; jump_instr2_off =
    false; push_sfi_halt_not_present = false; pop_sfi_not_aligned = true;
    set_sfi_registers_missing = false; after_call_label_missing = false;
    targets_not_aligned = false }

(** val set_set_sfi_registers_missing : comp_flags **)

let set_set_sfi_registers_missing =
  { store_instr_off = false; store_instr1_off = false; store_instr2_off =
    false; jump_instr_off = false; jump_instr1_off = false; jump_instr2_off =
    false; push_sfi_halt_not_present = false; pop_sfi_not_aligned = false;
    set_sfi_registers_missing = true; after_call_label_missing = false;
    targets_not_aligned = false }

(** val set_after_call_label_missing : comp_flags **)

let set_after_call_label_missing =
  { store_instr_off = false; store_instr1_off = false; store_instr2_off =
    false; jump_instr_off = false; jump_instr1_off = false; jump_instr2_off =
    false; push_sfi_halt_not_present = false; pop_sfi_not_aligned = false;
    set_sfi_registers_missing = false; after_call_label_missing = true;
    targets_not_aligned = false }

(** val set_targets_not_aligned : comp_flags **)

let set_targets_not_aligned =
  { store_instr_off = false; store_instr1_off = false; store_instr2_off =
    false; jump_instr_off = false; jump_instr1_off = false; jump_instr2_off =
    false; push_sfi_halt_not_present = false; pop_sfi_not_aligned = false;
    set_sfi_registers_missing = false; after_call_label_missing = false;
    targets_not_aligned = true }

(** val all_flags_off : comp_flags **)

let all_flags_off =
  { store_instr_off = false; store_instr1_off = false; store_instr2_off =
    false; jump_instr_off = false; jump_instr1_off = false; jump_instr2_off =
    false; push_sfi_halt_not_present = false; pop_sfi_not_aligned = false;
    set_sfi_registers_missing = false; after_call_label_missing = false;
    targets_not_aligned = false }

type component_id = int

type procedure_id = int

type block_id = int

type prog_int =
  (procedure_id list * (component_id * procedure_id) list) PMap.t

type compiler_env = { current_component : component_id; next_label : 
                      int; exported_procedures_labels : label0 PMap.t PMap.t;
                      cid2SFIid : SFIComponent.id PMap.t;
                      buffer2slot : int PMap.t PMap.t;
                      procId2slot : int PMap.t PMap.t; flags : comp_flags }

(** val current_component : compiler_env -> component_id **)

let current_component x = x.current_component

(** val next_label : compiler_env -> int **)

let next_label x = x.next_label

(** val exported_procedures_labels : compiler_env -> label0 PMap.t PMap.t **)

let exported_procedures_labels x = x.exported_procedures_labels

(** val cid2SFIid : compiler_env -> SFIComponent.id PMap.t **)

let cid2SFIid x = x.cid2SFIid

(** val buffer2slot : compiler_env -> int PMap.t PMap.t **)

let buffer2slot x = x.buffer2slot

(** val procId2slot : compiler_env -> int PMap.t PMap.t **)

let procId2slot x = x.procId2slot

(** val flags : compiler_env -> comp_flags **)

let flags x = x.flags

(** val with_current_component :
    component_id -> compiler_env -> compiler_env **)

let with_current_component cid env =
  { current_component = cid; next_label = env.next_label;
    exported_procedures_labels = env.exported_procedures_labels; cid2SFIid =
    env.cid2SFIid; buffer2slot = env.buffer2slot; procId2slot =
    env.procId2slot; flags = env.flags }

(** val env_add_blocks :
    component_id -> int PMap.t -> compiler_env -> compiler_env **)

let env_add_blocks cid blocks env =
  { current_component = env.current_component; next_label = env.next_label;
    exported_procedures_labels = env.exported_procedures_labels; cid2SFIid =
    env.cid2SFIid; buffer2slot = (PMap.add cid blocks env.buffer2slot);
    procId2slot = env.procId2slot; flags = env.flags }

(** val with_next_label : compiler_env -> compiler_env **)

let with_next_label env =
  { current_component = env.current_component; next_label =
    (N.add env.next_label 1); exported_procedures_labels =
    env.exported_procedures_labels; cid2SFIid = env.cid2SFIid; buffer2slot =
    env.buffer2slot; procId2slot = env.procId2slot; flags = env.flags }

(** val get_proc_label :
    component_id -> procedure_id -> (compiler_env, label0) CompStateMonad.t **)

let get_proc_label cid pid =
  bind0 (Obj.magic state_monad0) (Obj.magic CompStateMonad.get) (fun env ->
    match PMap.find cid env.exported_procedures_labels with
    | Some cprocs ->
      (match PMap.find pid cprocs with
       | Some res -> ret (Obj.magic state_monad0) res
       | None ->
         CompStateMonad.fail
           ('C'::('a'::('n'::(' '::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::(' '::('f'::('o'::('r'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::(' '::('i'::('n'::(' '::('e'::('x'::('p'::('o'::('r'::('t'::('e'::('d'::('_'::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::('s'::('_'::('l'::('a'::('b'::('e'::('l'::('s'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           (ExportedProcsLabelsP (cid, pid, env.exported_procedures_labels)))
    | None ->
      CompStateMonad.fail
        ('C'::('a'::('n'::(' '::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('c'::('o'::('m'::('p'::('o'::('e'::('n'::('t'::(' '::('i'::('n'::(' '::('e'::('x'::('p'::('o'::('r'::('t'::('e'::('d'::('_'::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::('s'::('_'::('l'::('a'::('b'::('e'::('l'::('s'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
        (ExportedProcsLabelsC (cid, env.exported_procedures_labels)))

(** val get_sfiId :
    component_id -> (compiler_env, SFIComponent.id) CompStateMonad.t **)

let get_sfiId cid =
  bind0 (Obj.magic state_monad0) (Obj.magic CompStateMonad.get) (fun env ->
    CompStateMonad.lift (PMap.find cid env.cid2SFIid)
      ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::(' '::('i'::('d'::(' '::('i'::('n'::(' '::('c'::('i'::('d'::('2'::('S'::('F'::('I'::('i'::('d'::[])))))))))))))))))))))))))))))))))
      (PosArg cid))

(** val get_SFI_code_address :
    component_id -> procedure_id -> int -> (compiler_env,
    RiscMachine.address) CompStateMonad.t **)

let get_SFI_code_address cid pid offset0 =
  bind0 (Obj.magic state_monad0) (Obj.magic CompStateMonad.get) (fun cenv ->
    bind0 (Obj.magic state_monad0) (get_sfiId cid) (fun sfiId ->
      bind0 (Obj.magic state_monad0)
        (CompStateMonad.lift (PMap.find cid (Obj.magic procId2slot cenv))
          ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::(' '::('i'::('d'::(' '::('i'::('n'::(' '::('p'::('r'::('o'::('c'::('I'::('d'::('2'::('s'::('l'::('o'::('t'::[])))))))))))))))))))))))))))))))))))
          (PosArg cid)) (fun cmap ->
        bind0 (Obj.magic state_monad0)
          (CompStateMonad.lift (PMap.find pid cmap)
            ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::(' '::('i'::('d'::(' '::('i'::('n'::(' '::('p'::('r'::('o'::('c'::('I'::('d'::('2'::('s'::('l'::('o'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))
            (TwoPosArg (cid, pid))) (fun slotid ->
          ret (Obj.magic state_monad0)
            (SFI.address_of sfiId slotid (N.of_nat offset0))))))

(** val get_data_slotid :
    component_id -> block_id -> (compiler_env, int) CompStateMonad.t **)

let get_data_slotid cid bid =
  bind0 (Obj.magic state_monad0) (Obj.magic CompStateMonad.get) (fun cenv ->
    bind0 (Obj.magic state_monad0)
      (CompStateMonad.lift (PMap.find cid (Obj.magic buffer2slot cenv))
        ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::(' '::('i'::('d'::(' '::('i'::('n'::(' '::('b'::('u'::('f'::('f'::('e'::('r'::('2'::('s'::('l'::('o'::('t'::[])))))))))))))))))))))))))))))))))))
        (PosArg cid)) (fun cmap ->
      CompStateMonad.lift (PMap.find bid cmap)
        ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('b'::('l'::('o'::('c'::('k'::(' '::('i'::('d'::(' '::('i'::('n'::(' '::('b'::('u'::('f'::('f'::('e'::('r'::('2'::('s'::('l'::('o'::('t'::[])))))))))))))))))))))))))))))))
        (TwoPosArg (cid, bid))))

(** val get_SFI_data_address :
    component_id -> block_id -> Block.offset -> (compiler_env,
    RiscMachine.address) CompStateMonad.t **)

let get_SFI_data_address cid bid offset0 =
  bind0 (Obj.magic state_monad0) (Obj.magic CompStateMonad.get) (fun _ ->
    bind0 (Obj.magic state_monad0) (get_sfiId cid) (fun psfiId ->
      bind0 (Obj.magic state_monad0) (get_data_slotid cid bid)
        (fun pslotid ->
        ret (Obj.magic state_monad0)
          (SFI.address_of psfiId pslotid (Z.to_N offset0)))))

(** val gen_cn : prog_int -> component_id list **)

let gen_cn pi =
  map (fun pat -> let (key0, _) = pat in key0) (PMap.elements pi)

(** val exported_procs_labels :
    code PMap.t PMap.t -> prog_int -> label0 PMap.t PMap.t **)

let exported_procs_labels procs pi =
  let max_code_component_label = fun procs0 ->
    (fold_left Coq_Pos.max
      (map (fun i -> match i with
                     | ILabel lbl -> Coq_Pos.of_nat lbl
                     | _ -> 1) (flat_map snd procs0)) 1)
  in
  let component_exported_procs_labels = fun cid pi0 procs0 ->
    match PMap.find cid pi0 with
    | Some y ->
      let (exp_procs, _) = y in
      let start_lbl = N.add (max_code_component_label procs0) 1 in
      let new_labels =
        map N.of_nat (seq (N.to_nat start_lbl) (length exp_procs))
      in
      PMapExtra.of_list
        (combine exp_procs
          (combine (repeat cid (length exp_procs)) new_labels))
    | None -> PMap.empty
  in
  PMap.fold (fun cid procs_map acc ->
    PMap.add cid
      (component_exported_procs_labels cid pi (PMap.elements procs_map)) acc)
    procs PMap.empty

(** val allocate_procedure_slots : code PMap.t PMap.t -> int PMap.t PMap.t **)

let rec allocate_procedure_slots procs =
  PMapExtra.of_list
    (map (fun pat ->
      let (cid, proc_map) = pat in
      let pids = map fst (PMap.elements proc_map) in
      (cid,
      (PMapExtra.of_list
        (combine pids (SFI.Allocator.allocate_code_slots (length pids))))))
      (PMap.elements procs))

(** val init_env :
    comp_flags -> int PMap.t -> int PMap.t PMap.t -> label0 PMap.t PMap.t ->
    int -> compiler_env **)

let init_env i_flags i_cid2SFIid i_procId2slot i_exported_procedures_labels i_next_label =
  { current_component = 1; next_label = i_next_label;
    exported_procedures_labels = i_exported_procedures_labels; cid2SFIid =
    i_cid2SFIid; buffer2slot = PMap.empty; procId2slot = i_procId2slot;
    flags = i_flags }

(** val allocate_buffers :
    (component_id * (block_id * (int, value list) sum) list) list ->
    (compiler_env, RiscMachine.Memory.t) CompStateMonad.t **)

let rec allocate_buffers buffs =
  let allocate_buffers1 = fun buffs0 ->
    match buffs0 with
    | [] -> ret state_monad0 RiscMachine.Memory.empty
    | y :: xs ->
      let (cid, lst) = y in
      bind0 state_monad0 (Obj.magic allocate_buffers xs) (fun mem1 ->
        bind0 state_monad0 (Obj.magic get_sfiId cid) (fun sfi_cid ->
          match find (fun pat ->
                  let (_, size1) = pat in
                  (match size1 with
                   | Inl nsz -> Nat.ltb (N.to_nat SFI.coq_SLOT_SIZE) nsz
                   | Inr lst0 ->
                     Nat.ltb (N.to_nat SFI.coq_SLOT_SIZE) (length lst0))) lst with
          | Some _ ->
            CompStateMonad.fail
              ('a'::('l'::('l'::('o'::('c'::('a'::('t'::('e'::('_'::('b'::('u'::('f'::('f'::('e'::('r'::('s'::[]))))))))))))))))
              NoInfo
          | None ->
            let blocks =
              PMapExtra.of_list
                (combine (fst (split lst))
                  (SFI.Allocator.allocate_data_slots (length lst)))
            in
            bind0 state_monad0
              (Obj.magic CompStateMonad.modify (env_add_blocks cid blocks))
              (fun _ ->
              ret state_monad0
                (RiscMachine.Memory.set_value mem1
                  (SFI.address_of sfi_cid SFI.Allocator.allocator_data_slot 0)
                  (SFI.Allocator.initial_allocator_value (length lst))))))
  in
  let allocator_init =
    let rec allocator_init cids mem1 =
      match cids with
      | [] -> ret state_monad0 mem1
      | cid :: xs ->
        bind0 state_monad0 (allocator_init xs mem1) (fun res_mem ->
          bind0 state_monad0 (Obj.magic CompStateMonad.get) (fun _ ->
            bind0 state_monad0 (Obj.magic get_sfiId cid) (fun sfi_cid ->
              ret state_monad0
                (RiscMachine.Memory.set_value res_mem
                  (SFI.address_of sfi_cid SFI.Allocator.allocator_data_slot 0)
                  (SFI.Allocator.initial_allocator_value 0)))))
    in allocator_init
  in
  bind0 (Obj.magic state_monad0) (Obj.magic allocate_buffers1 buffs)
    (fun mem1 ->
    bind0 (Obj.magic state_monad0) (Obj.magic CompStateMonad.get)
      (fun cenv ->
      Obj.magic allocator_init
        (filter (fun id0 -> negb (existsb (Coq_Pos.eqb id0) (map fst buffs)))
          (map fst (PMap.elements cenv.cid2SFIid))) mem1))

(** val init_buffers :
    RiscMachine.Memory.t -> (component_id * (block_id * (int, value list)
    sum) list) list -> (compiler_env, RiscMachine.Memory.t) CompStateMonad.t **)

let rec init_buffers mem1 buffs =
  let init_buffer =
    let rec init_buffer mem2 sfi_cid slotid = function
    | [] -> ret state_monad0 mem2
    | y :: xs ->
      let (off, imval) = y in
      (match imval with
       | Int n ->
         init_buffer
           (RiscMachine.Memory.set_value mem2
             (SFI.address_of sfi_cid slotid (N.of_nat off)) n) sfi_cid slotid
           xs
       | Ptr p ->
         let cid = Coq_Pos.of_nat (Pointer.component p) in
         let bid = Coq_Pos.of_nat (Pointer.block p) in
         let offset0 = Pointer.offset p in
         if Z.ltb offset0 0
         then CompStateMonad.fail
                ('i'::('n'::('i'::('t'::('_'::('b'::('u'::('f'::('f'::('e'::('r'::('s'::(' '::('n'::('e'::('g'::('a'::('t'::('i'::('v'::('e'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::(' '::('f'::('o'::('r'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))))))
                (TwoPosArg (cid, bid))
         else if Z.leb (Z.of_N SFI.coq_SLOT_SIZE) offset0
              then CompStateMonad.fail
                     ('i'::('n'::('i'::('t'::('_'::('b'::('u'::('f'::('f'::('e'::('r'::('s'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::(' '::('t'::('o'::('o'::(' '::('l'::('a'::('r'::('g'::('e'::[])))))))))))))))))))))))))))))
                     (TwoPosArg (cid, bid))
              else bind0 state_monad0
                     (Obj.magic get_SFI_data_address cid bid offset0)
                     (fun address0 ->
                     init_buffer
                       (RiscMachine.Memory.set_value mem2
                         (SFI.address_of sfi_cid slotid (N.of_nat off))
                         (RiscMachine.to_value address0)) sfi_cid slotid xs)
       | Undef -> init_buffer mem2 sfi_cid slotid xs)
    in init_buffer
  in
  let init_buffers_comp =
    let rec init_buffers_comp mem2 cid = function
    | [] -> ret state_monad0 mem2
    | p :: xs ->
      let (bid, elt) = p in
      (match elt with
       | Inl _ -> ret state_monad0 mem2
       | Inr vals ->
         bind0 state_monad0 (Obj.magic CompStateMonad.get) (fun _ ->
           bind0 state_monad0 (Obj.magic get_sfiId cid) (fun sfi_cid ->
             bind0 state_monad0 (Obj.magic get_data_slotid cid bid)
               (fun slotid ->
               bind0 state_monad0
                 (init_buffer mem2 sfi_cid slotid
                   (combine (seq 0 (length vals)) vals)) (fun mem' ->
                 init_buffers_comp mem' cid xs)))))
    in init_buffers_comp
  in
  (match buffs with
   | [] -> ret (Obj.magic state_monad0) mem1
   | p :: xs ->
     let (cid, lst) = p in
     bind0 (Obj.magic state_monad0)
       (Obj.magic init_buffers_comp mem1 cid lst) (fun mem' ->
       init_buffers mem' xs))

(** val sfi_top_address :
    RiscMachine.Register.t -> SFIComponent.id -> code0 **)

let sfi_top_address rd cid =
  (IConst0
    ((RiscMachine.to_value (SFI.or_data_mask SFI.coq_MONITOR_COMPONENT_ID)),
    RiscMachine.Register.coq_R_OR_DATA_MASK)) :: ((IConst0
    ((RiscMachine.to_value
       (N.add (N.add SFI.coq_OFFSET_BITS_NO SFI.coq_COMP_BITS_NO) 1)),
    rd)) :: ((IBinOp0 (RiscMachine.ISA.ShiftLeft,
    RiscMachine.Register.coq_R_SFI_SP, rd, rd)) :: ((IBinOp0
    (RiscMachine.ISA.BitwiseOr, rd, RiscMachine.Register.coq_R_OR_DATA_MASK,
    rd)) :: ((IConst0 ((RiscMachine.to_value (SFI.or_data_mask cid)),
    RiscMachine.Register.coq_R_OR_DATA_MASK)) :: []))))

(** val gen_push_sfi : SFIComponent.id -> code0 **)

let gen_push_sfi cid =
  app (sfi_top_address RiscMachine.Register.coq_R_AUX1 cid) ((IStore0
    (RiscMachine.Register.coq_R_AUX1,
    RiscMachine.Register.coq_R_RA)) :: ((IConst0 (1,
    RiscMachine.Register.coq_R_AUX1)) :: ((IBinOp0 (RiscMachine.ISA.Addition,
    RiscMachine.Register.coq_R_SFI_SP, RiscMachine.Register.coq_R_AUX1,
    RiscMachine.Register.coq_R_SFI_SP)) :: [])))

(** val gen_pop_sfi : (compiler_env, code0) CompStateMonad.t **)

let gen_pop_sfi =
  bind0 (Obj.magic state_monad0) (Obj.magic CompStateMonad.get) (fun cenv ->
    bind0 (Obj.magic state_monad0)
      (Obj.magic get_sfiId cenv.current_component) (fun cid ->
      bind0 (Obj.magic state_monad0)
        (Obj.magic CompStateMonad.modify with_next_label) (fun _ ->
        let lbl = (cenv.current_component, cenv.next_label) in
        ret (Obj.magic state_monad0)
          (app
            (if cenv.flags.pop_sfi_not_aligned
             then []
             else (ILabel0 lbl) :: [])
            (app ((IConst0 (1, RiscMachine.Register.coq_R_RA)) :: ((IBinOp0
              (RiscMachine.ISA.Subtraction,
              RiscMachine.Register.coq_R_SFI_SP,
              RiscMachine.Register.coq_R_RA,
              RiscMachine.Register.coq_R_SFI_SP)) :: []))
              (app (sfi_top_address RiscMachine.Register.coq_R_RA cid)
                ((ILoad0 (RiscMachine.Register.coq_R_RA,
                RiscMachine.Register.coq_R_RA)) :: [])))))))

(** val gen_set_sfi_registers :
    SFIComponent.id -> (compiler_env, code0) CompStateMonad.t **)

let gen_set_sfi_registers cid =
  bind0 (Obj.magic state_monad0) (Obj.magic CompStateMonad.get) (fun cenv ->
    let data_mask = RiscMachine.to_value (SFI.or_data_mask cid) in
    let code_mask = RiscMachine.to_value (SFI.or_code_mask cid) in
    if cenv.flags.set_sfi_registers_missing
    then ret (Obj.magic state_monad0) []
    else ret (Obj.magic state_monad0) ((IConst0 (data_mask,
           RiscMachine.Register.coq_R_OR_DATA_MASK)) :: ((IConst0 (code_mask,
           RiscMachine.Register.coq_R_OR_CODE_MASK)) :: ((IConst0 (data_mask,
           RiscMachine.Register.coq_R_D)) :: ((IConst0 (code_mask,
           RiscMachine.Register.coq_R_T)) :: [])))))

(** val compile_IConst :
    imvalue -> register -> (compiler_env, code0) CompStateMonad.t **)

let compile_IConst imval reg =
  let reg' = map_register reg in
  (match imval with
   | IInt n -> ret (Obj.magic state_monad0) ((IConst0 (n, reg')) :: [])
   | IPtr p ->
     let cid = Coq_Pos.of_nat (Pointer.component p) in
     let bid = Coq_Pos.of_nat (Pointer.block p) in
     let offset0 = Pointer.offset p in
     if Z.ltb offset0 0
     then CompStateMonad.fail
            ('c'::('o'::('m'::('p'::('i'::('l'::('e'::('_'::('I'::('C'::('o'::('n'::('s'::('t'::(' '::('n'::('e'::('g'::('a'::('t'::('i'::('v'::('e'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::(' '::('f'::('o'::('r'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::(' '::[])))))))))))))))))))))))))))))))))))))))))))
            (TwoPosArg (cid, bid))
     else if Z.leb (Z.of_N SFI.coq_SLOT_SIZE) offset0
          then CompStateMonad.fail
                 ('c'::('o'::('m'::('p'::('i'::('l'::('e'::('_'::('I'::('C'::('o'::('n'::('s'::('t'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::(' '::('t'::('o'::('o'::(' '::('l'::('a'::('r'::('g'::('e'::[])))))))))))))))))))))))))))))))
                 (TwoPosArg (cid, bid))
          else bind0 (Obj.magic state_monad0)
                 (Obj.magic get_SFI_data_address cid bid offset0)
                 (fun address0 ->
                 ret (Obj.magic state_monad0) ((IConst0
                   ((RiscMachine.to_value address0), reg')) :: [])))

(** val compile_IStore :
    register -> register -> (compiler_env, code0) CompStateMonad.t **)

let compile_IStore rp rs =
  bind0 (Obj.magic state_monad0) (Obj.magic CompStateMonad.get) (fun cenv ->
    let cf = cenv.flags in
    if cf.store_instr_off
    then ret (Obj.magic state_monad0) ((IStore0 ((map_register rp),
           (map_register rs))) :: [])
    else if cf.store_instr1_off
         then ret (Obj.magic state_monad0) ((IBinOp0
                (RiscMachine.ISA.BitwiseOr, (map_register rp),
                RiscMachine.Register.coq_R_OR_DATA_MASK,
                RiscMachine.Register.coq_R_D)) :: ((IStore0
                (RiscMachine.Register.coq_R_D, (map_register rs))) :: []))
         else if cf.store_instr2_off
              then ret (Obj.magic state_monad0) ((IBinOp0
                     (RiscMachine.ISA.BitwiseAnd, (map_register rp),
                     RiscMachine.Register.coq_R_AND_DATA_MASK,
                     RiscMachine.Register.coq_R_D)) :: ((IStore0
                     (RiscMachine.Register.coq_R_D,
                     (map_register rs))) :: []))
              else ret (Obj.magic state_monad0) ((IBinOp0
                     (RiscMachine.ISA.BitwiseAnd, (map_register rp),
                     RiscMachine.Register.coq_R_AND_DATA_MASK,
                     RiscMachine.Register.coq_R_D)) :: ((IBinOp0
                     (RiscMachine.ISA.BitwiseOr,
                     RiscMachine.Register.coq_R_D,
                     RiscMachine.Register.coq_R_OR_DATA_MASK,
                     RiscMachine.Register.coq_R_D)) :: ((IStore0
                     (RiscMachine.Register.coq_R_D,
                     (map_register rs))) :: []))))

(** val compile_IJump : register -> (compiler_env, code0) CompStateMonad.t **)

let compile_IJump rt =
  bind0 (Obj.magic state_monad0) (Obj.magic CompStateMonad.get) (fun cenv ->
    let cf = cenv.flags in
    if cf.jump_instr_off
    then ret (Obj.magic state_monad0) ((IJump0 (map_register rt)) :: [])
    else if cf.jump_instr1_off
         then ret (Obj.magic state_monad0) ((IBinOp0
                (RiscMachine.ISA.BitwiseOr, (map_register rt),
                RiscMachine.Register.coq_R_OR_CODE_MASK,
                RiscMachine.Register.coq_R_T)) :: ((IJump0
                RiscMachine.Register.coq_R_T) :: []))
         else if cf.jump_instr2_off
              then ret (Obj.magic state_monad0) ((IBinOp0
                     (RiscMachine.ISA.BitwiseAnd, (map_register rt),
                     RiscMachine.Register.coq_R_AND_CODE_MASK,
                     RiscMachine.Register.coq_R_T)) :: ((IJump0
                     RiscMachine.Register.coq_R_T) :: []))
              else ret (Obj.magic state_monad0) ((IBinOp0
                     (RiscMachine.ISA.BitwiseAnd, (map_register rt),
                     RiscMachine.Register.coq_R_AND_CODE_MASK,
                     RiscMachine.Register.coq_R_T)) :: ((IBinOp0
                     (RiscMachine.ISA.BitwiseOr,
                     RiscMachine.Register.coq_R_T,
                     RiscMachine.Register.coq_R_OR_CODE_MASK,
                     RiscMachine.Register.coq_R_T)) :: ((IJump0
                     RiscMachine.Register.coq_R_T) :: []))))

(** val ireg_eqb : register -> register -> bool **)

let ireg_eqb r1 r2 =
  match r1 with
  | R_ONE -> (match r2 with
              | R_ONE -> true
              | _ -> false)
  | R_COM -> (match r2 with
              | R_COM -> true
              | _ -> false)
  | R_AUX1 -> (match r2 with
               | R_AUX1 -> true
               | _ -> false)
  | R_AUX2 -> (match r2 with
               | R_AUX2 -> true
               | _ -> false)
  | R_RA -> (match r2 with
             | R_RA -> true
             | _ -> false)
  | R_SP -> (match r2 with
             | R_SP -> true
             | _ -> false)

(** val compile_IAlloc :
    register -> register -> (compiler_env, code0) CompStateMonad.t **)

let compile_IAlloc rp rs =
  bind0 (Obj.magic state_monad0) (Obj.magic CompStateMonad.get) (fun cenv ->
    bind0 (Obj.magic state_monad0)
      (Obj.magic get_sfiId cenv.current_component) (fun cid ->
      if ireg_eqb rp rs
      then if ireg_eqb rp R_AUX1
           then let r1 = R_AUX1 in
                let r2 = R_AUX2 in
                bind0 (Obj.magic state_monad0) (compile_IStore r1 r2)
                  (fun store_r1_r2 ->
                  bind0 (Obj.magic state_monad0) (compile_IStore r2 r1)
                    (fun store_r2_r1 ->
                    let r3 = map_register r1 in
                    let r4 = map_register r2 in
                    ret (Obj.magic state_monad0)
                      (app ((IConst0
                        ((RiscMachine.to_value (SFI.address_of cid 1 1)),
                        r3)) :: [])
                        (app store_r1_r2
                          (app ((IConst0
                            ((RiscMachine.to_value (SFI.address_of cid 1 0)),
                            r4)) :: ((ILoad0 (r4, r3)) :: ((IConst0 (1,
                            r4)) :: ((IBinOp0 (RiscMachine.ISA.Addition, r3,
                            r4, r3)) :: ((IConst0
                            ((RiscMachine.to_value (SFI.address_of cid 1 0)),
                            r4)) :: [])))))
                            (app store_r2_r1 ((IConst0
                              ((RiscMachine.to_value
                                 (N.add
                                   (N.add SFI.coq_OFFSET_BITS_NO
                                     SFI.coq_COMP_BITS_NO) 1)),
                              r4)) :: ((IBinOp0 (RiscMachine.ISA.ShiftLeft,
                              r3, r4, r3)) :: ((IBinOp0
                              (RiscMachine.ISA.BitwiseOr, r3,
                              RiscMachine.Register.coq_R_OR_DATA_MASK,
                              r3)) :: ((IConst0
                              ((RiscMachine.to_value (SFI.address_of cid 1 1)),
                              r4)) :: ((ILoad0 (r4, r4)) :: [])))))))))))
           else let r2 = R_AUX1 in
                bind0 (Obj.magic state_monad0) (compile_IStore rp r2)
                  (fun store_r1_r2 ->
                  bind0 (Obj.magic state_monad0) (compile_IStore r2 rp)
                    (fun store_r2_r1 ->
                    let r1 = map_register rp in
                    let r3 = map_register r2 in
                    ret (Obj.magic state_monad0)
                      (app ((IConst0
                        ((RiscMachine.to_value (SFI.address_of cid 1 1)),
                        r1)) :: [])
                        (app store_r1_r2
                          (app ((IConst0
                            ((RiscMachine.to_value (SFI.address_of cid 1 0)),
                            r3)) :: ((ILoad0 (r3, r1)) :: ((IConst0 (1,
                            r3)) :: ((IBinOp0 (RiscMachine.ISA.Addition, r1,
                            r3, r1)) :: ((IConst0
                            ((RiscMachine.to_value (SFI.address_of cid 1 0)),
                            r3)) :: [])))))
                            (app store_r2_r1 ((IConst0
                              ((RiscMachine.to_value
                                 (N.add
                                   (N.add SFI.coq_OFFSET_BITS_NO
                                     SFI.coq_COMP_BITS_NO) 1)),
                              r3)) :: ((IBinOp0 (RiscMachine.ISA.ShiftLeft,
                              r1, r3, r1)) :: ((IBinOp0
                              (RiscMachine.ISA.BitwiseOr, r1,
                              RiscMachine.Register.coq_R_OR_DATA_MASK,
                              r1)) :: ((IConst0
                              ((RiscMachine.to_value (SFI.address_of cid 1 1)),
                              r3)) :: ((ILoad0 (r3, r3)) :: [])))))))))))
      else bind0 (Obj.magic state_monad0) (compile_IStore rp rs)
             (fun store_r1_r2 ->
             bind0 (Obj.magic state_monad0) (compile_IStore rs rp)
               (fun store_r2_r1 ->
               let r1 = map_register rp in
               let r2 = map_register rs in
               ret (Obj.magic state_monad0)
                 (app ((IConst0
                   ((RiscMachine.to_value (SFI.address_of cid 1 1)),
                   r1)) :: [])
                   (app store_r1_r2
                     (app ((IConst0
                       ((RiscMachine.to_value (SFI.address_of cid 1 0)),
                       r2)) :: ((ILoad0 (r2, r1)) :: ((IConst0 (1,
                       r2)) :: ((IBinOp0 (RiscMachine.ISA.Addition, r1, r2,
                       r1)) :: ((IConst0
                       ((RiscMachine.to_value (SFI.address_of cid 1 0)),
                       r2)) :: [])))))
                       (app store_r2_r1 ((IConst0
                         ((RiscMachine.to_value
                            (N.add
                              (N.add SFI.coq_OFFSET_BITS_NO
                                SFI.coq_COMP_BITS_NO) 1)), r2)) :: ((IBinOp0
                         (RiscMachine.ISA.ShiftLeft, r1, r2,
                         r1)) :: ((IBinOp0 (RiscMachine.ISA.BitwiseOr, r1,
                         RiscMachine.Register.coq_R_OR_DATA_MASK,
                         r1)) :: ((IConst0
                         ((RiscMachine.to_value (SFI.address_of cid 1 1)),
                         r2)) :: ((ILoad0 (r2, r2)) :: [])))))))))))))

(** val compile_IReturn : (compiler_env, code0) CompStateMonad.t **)

let compile_IReturn =
  bind0 (Obj.magic state_monad0) gen_pop_sfi (fun res ->
    ret (Obj.magic state_monad0)
      (app res ((IJump0 RiscMachine.Register.coq_R_RA) :: [])))

(** val compile_ICall :
    component_id -> procedure_id -> (compiler_env, code0) CompStateMonad.t **)

let compile_ICall cid1 pid =
  bind0 (Obj.magic state_monad0) (Obj.magic CompStateMonad.get) (fun cenv ->
    bind0 (Obj.magic state_monad0)
      (Obj.magic get_sfiId cenv.current_component) (fun cid ->
      bind0 (Obj.magic state_monad0) (Obj.magic get_proc_label cid1 pid)
        (fun clbl ->
        bind0 (Obj.magic state_monad0)
          (Obj.magic CompStateMonad.modify with_next_label) (fun _ ->
          let lbl = (cenv.current_component, cenv.next_label) in
          bind0 (Obj.magic state_monad0) (gen_set_sfi_registers cid)
            (fun sfi_regs_code ->
            ret (Obj.magic state_monad0)
              (app ((IJal0 clbl) :: [])
                (app
                  (if cenv.flags.after_call_label_missing
                   then []
                   else (ILabel0 lbl) :: []) sfi_regs_code)))))))

(** val compile_instructions :
    code -> (compiler_env, code0) CompStateMonad.t **)

let rec compile_instructions ilist =
  let compile_instruction = fun i ->
    bind0 state_monad0 (Obj.magic CompStateMonad.get) (fun cenv ->
      let cid = cenv.current_component in
      (match i with
       | INop -> ret state_monad0 (INop0 :: [])
       | ILabel lbl ->
         ret state_monad0 ((ILabel0 (cid, (N.of_nat lbl))) :: [])
       | IConst (imval, reg) -> Obj.magic compile_IConst imval reg
       | IMov (rs, rd) ->
         ret state_monad0 ((IMov0 ((map_register rs),
           (map_register rd))) :: [])
       | IBinOp (op0, r1, r2, rd) ->
         ret state_monad0 ((IBinOp0 ((map_binop op0), (map_register r1),
           (map_register r2), (map_register rd))) :: [])
       | ILoad (rp, rd) ->
         ret state_monad0 ((ILoad0 ((map_register rp),
           (map_register rd))) :: [])
       | IStore (rp, rs) -> Obj.magic compile_IStore rp rs
       | IAlloc (rp, rs) -> Obj.magic compile_IAlloc rp rs
       | IBnz (r, lbl) ->
         ret state_monad0 ((IBnz0 ((map_register r), (cid,
           (N.of_nat lbl)))) :: [])
       | IJump rt -> Obj.magic compile_IJump rt
       | IJal lbl -> ret state_monad0 ((IJal0 (cid, (N.of_nat lbl))) :: [])
       | ICall (c, p) ->
         Obj.magic compile_ICall (Coq_Pos.of_nat c) (Coq_Pos.of_nat p)
       | IReturn -> Obj.magic compile_IReturn
       | IHalt -> ret state_monad0 (IHalt0 :: [])))
  in
  (match ilist with
   | [] -> ret (Obj.magic state_monad0) []
   | i :: xs ->
     bind0 (Obj.magic state_monad0) (Obj.magic compile_instruction i)
       (fun ai ->
       bind0 (Obj.magic state_monad0) (compile_instructions xs) (fun res ->
         ret (Obj.magic state_monad0) (app ai res))))

(** val compile_procedure :
    procedure_id -> code -> prog_int -> (compiler_env, code0) CompStateMonad.t **)

let compile_procedure pid code1 interface0 =
  bind0 (Obj.magic state_monad0) (Obj.magic CompStateMonad.get) (fun cenv ->
    let cid = cenv.current_component in
    bind0 (Obj.magic state_monad0)
      (CompStateMonad.lift (PMap.find cid (Obj.magic interface0))
        ('C'::('a'::('n'::('\''::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('i'::('n'::('t'::('e'::('r'::('f'::('a'::('c'::('e'::(' '::('f'::('o'::('r'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::(' '::[])))))))))))))))))))))))))))))))))))
        (PosArg cid)) (fun comp_interface ->
      let exported_procs = fst comp_interface in
      let is_exported = existsb (Coq_Pos.eqb pid) exported_procs in
      bind0 (Obj.magic state_monad0) (compile_instructions code1)
        (fun acode ->
        if is_exported
        then bind0 (Obj.magic state_monad0)
               (Obj.magic get_proc_label cid pid) (fun proc_label ->
               bind0 (Obj.magic state_monad0) (Obj.magic get_sfiId cid)
                 (fun sfiId ->
                 bind0 (Obj.magic state_monad0) (gen_set_sfi_registers sfiId)
                   (fun sfi_regs_code ->
                   ret (Obj.magic state_monad0)
                     (app
                       (if cenv.flags.push_sfi_halt_not_present
                        then []
                        else IHalt0 :: [])
                       (app ((ILabel0 proc_label) :: [])
                         (app (gen_push_sfi sfiId) (app sfi_regs_code acode)))))))
        else ret (Obj.magic state_monad0) acode)))

(** val check_component_labels :
    component_id -> (procedure_id * code0) list -> (compiler_env,
    (procedure_id * code0) list) CompStateMonad.t **)

let check_component_labels cid procs =
  let check_procedure = fun _ _ acode ->
    match acode with
    | [] ->
      CompStateMonad.fail
        (' '::('c'::('h'::('e'::('c'::('k'::('_'::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::('_'::('l'::('a'::('b'::('e'::('l'::('s'::(':'::(':'::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('t'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        NoInfo
    | _ :: l ->
      (match l with
       | [] ->
         CompStateMonad.fail
           (' '::('c'::('h'::('e'::('c'::('k'::('_'::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::('_'::('l'::('a'::('b'::('e'::('l'::('s'::(':'::(':'::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('t'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           NoInfo
       | y :: _ ->
         (match y with
          | ILabel0 _ -> ret state_monad0 procs
          | _ ->
            CompStateMonad.fail
              (' '::('c'::('h'::('e'::('c'::('k'::('_'::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::('_'::('l'::('a'::('b'::('e'::('l'::('s'::(':'::(':'::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('t'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              NoInfo))
  in
  let check_component =
    let rec check_component cid0 procs0 = match procs0 with
    | [] -> ret state_monad0 procs0
    | y :: xs ->
      let (pid, acode) = y in
      bind0 state_monad0 (check_procedure cid0 pid acode) (fun _ ->
        check_component cid0 xs)
    in check_component
  in
  Obj.magic check_component cid procs

(** val compile_components :
    (component_id * code PMap.t) list -> prog_int -> (compiler_env,
    (component_id * code0 PMap.t) list) CompStateMonad.t **)

let rec compile_components components interface0 =
  let compile_procedures =
    let rec compile_procedures procs interface1 =
      match procs with
      | [] -> ret state_monad0 []
      | y :: xs ->
        let (pid, code1) = y in
        bind0 state_monad0 (Obj.magic compile_procedure pid code1 interface1)
          (fun compiled_proc ->
          bind0 state_monad0 (compile_procedures xs interface1) (fun res ->
            ret state_monad0 ((pid, compiled_proc) :: res)))
    in compile_procedures
  in
  (match components with
   | [] -> ret (Obj.magic state_monad0) []
   | p :: xs ->
     let (cid, procs) = p in
     bind0 (Obj.magic state_monad0)
       (Obj.magic CompStateMonad.modify (with_current_component cid))
       (fun _ ->
       bind0 (Obj.magic state_monad0)
         (Obj.magic compile_procedures (PMap.elements procs) interface0)
         (fun procs0 ->
         bind0 (Obj.magic state_monad0)
           (Obj.magic check_component_labels cid procs0) (fun _ ->
           bind0 (Obj.magic state_monad0) (compile_components xs interface0)
             (fun res ->
             ret (Obj.magic state_monad0) ((cid,
               (PMapExtra.of_list procs0)) :: res))))))

(** val layout_procedure :
    comp_flags -> component_id -> procedure_id -> label0 -> code0 -> lcode **)

let layout_procedure cf _ _ plbl code1 =
  let padd = fun acc elt ->
    let r = N.modulo (N.of_nat (length acc)) SFI.coq_BASIC_BLOCK_SIZE in
    let p =
      N.modulo (N.sub SFI.coq_BASIC_BLOCK_SIZE r) SFI.coq_BASIC_BLOCK_SIZE
    in
    app acc (app (repeat (None, INop0) (N.to_nat p)) (elt :: []))
  in
  let lcode1 =
    map (fun pat ->
      let (ll, i) = pat in
      (match ll with
       | [] -> (None, i)
       | _ :: _ -> ((Some ll), i)))
      (snd
        (fold_left (fun acc elt ->
          let (current_labels, lcode0) = acc in
          (match elt with
           | INop0 -> ([], (app lcode0 ((current_labels, elt) :: [])))
           | ILabel0 lbl -> ((app current_labels (lbl :: [])), lcode0)
           | _ -> ([], (app lcode0 ((current_labels, elt) :: []))))) code1
          ([], [])))
  in
  if cf.targets_not_aligned
  then lcode1
  else fold_left (fun acc elt ->
         let (y, _) = elt in
         (match y with
          | Some ll ->
            (match ll with
             | [] -> app acc (elt :: [])
             | lbl :: l ->
               (match l with
                | [] ->
                  if label_eqb lbl plbl
                  then app acc (elt :: [])
                  else padd acc elt
                | _ :: _ -> padd acc elt))
          | None -> app acc (elt :: []))) lcode1 []

(** val check_label_duplication : component_id -> lcode PMap.t -> bool **)

let check_label_duplication _ procs =
  let all_labels =
    fold_left (fun acc pat ->
      let (_, lcode0) = pat in
      fold_left (fun acc' linstr ->
        let (y, _) = linstr in
        (match y with
         | Some ll -> app acc' ll
         | None -> acc')) lcode0 acc) (PMap.elements procs) []
  in
  (=) (length all_labels) (length (nodup label_eq_dec all_labels))

(** val check_labeled_code :
    lcode PMap.t PMap.t -> (compiler_env, lcode PMap.t PMap.t)
    CompStateMonad.t **)

let check_labeled_code labeled_code =
  let check_procedure = fun cid pid lcode0 ->
    bind0 state_monad0 (Obj.magic get_proc_label cid pid) (fun _ ->
      match lcode0 with
      | [] ->
        CompStateMonad.fail
          (' '::('c'::('h'::('e'::('c'::('k'::('_'::('l'::('a'::('b'::('e'::('l'::('e'::('d'::('_'::('c'::('o'::('d'::('e'::(':'::(':'::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('t'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::(' '::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (DuplicatedLabels labeled_code)
      | _ :: l ->
        (match l with
         | [] ->
           CompStateMonad.fail
             (' '::('c'::('h'::('e'::('c'::('k'::('_'::('l'::('a'::('b'::('e'::('l'::('e'::('d'::('_'::('c'::('o'::('d'::('e'::(':'::(':'::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('t'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::(' '::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))
             (DuplicatedLabels labeled_code)
         | y :: _ ->
           let (y0, _) = y in
           (match y0 with
            | Some y1 ->
              (match y1 with
               | [] ->
                 CompStateMonad.fail
                   (' '::('c'::('h'::('e'::('c'::('k'::('_'::('l'::('a'::('b'::('e'::('l'::('e'::('d'::('_'::('c'::('o'::('d'::('e'::(':'::(':'::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('t'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::(' '::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                   (DuplicatedLabels labeled_code)
               | _ :: l0 ->
                 (match l0 with
                  | [] -> ret state_monad0 labeled_code
                  | _ :: _ ->
                    CompStateMonad.fail
                      (' '::('c'::('h'::('e'::('c'::('k'::('_'::('l'::('a'::('b'::('e'::('l'::('e'::('d'::('_'::('c'::('o'::('d'::('e'::(':'::(':'::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('t'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::(' '::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                      (DuplicatedLabels labeled_code)))
            | None ->
              CompStateMonad.fail
                (' '::('c'::('h'::('e'::('c'::('k'::('_'::('l'::('a'::('b'::('e'::('l'::('e'::('d'::('_'::('c'::('o'::('d'::('e'::(':'::(':'::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('t'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::(' '::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                (DuplicatedLabels labeled_code))))
  in
  let check_component =
    let rec check_component cid = function
    | [] -> ret state_monad0 labeled_code
    | y :: xs ->
      let (pid, lcode0) = y in
      bind0 state_monad0 (check_procedure cid pid lcode0) (fun _ ->
        check_component cid xs)
    in check_component
  in
  let check_progr =
    let rec check_progr = function
    | [] -> ret state_monad0 labeled_code
    | y :: xs ->
      let (cid, comp) = y in
      bind0 state_monad0 (check_component cid (PMap.elements comp)) (fun _ ->
        if check_label_duplication cid comp
        then check_progr xs
        else CompStateMonad.fail
               (' '::('c'::('h'::('e'::('c'::('k'::('_'::('l'::('a'::('b'::('e'::('l'::('e'::('d'::('_'::('c'::('o'::('d'::('e'::(':'::(':'::('l'::('a'::('b'::('e'::('l'::(' '::('d'::('u'::('p'::('l'::('i'::('c'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('n'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::(' '::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
               (DuplicatedLabels labeled_code))
    in check_progr
  in
  Obj.magic check_progr (PMap.elements labeled_code)

(** val layout_code :
    comp_flags -> code0 PMap.t PMap.t -> (compiler_env, lcode PMap.t PMap.t)
    CompStateMonad.t **)

let layout_code cf acode =
  let layout_procedures =
    let rec layout_procedures cid = function
    | [] -> ret state_monad0 PMap.empty
    | y :: xs ->
      let (pid, code1) = y in
      bind0 state_monad0 (layout_procedures cid xs) (fun res_map ->
        bind0 state_monad0 (Obj.magic get_proc_label cid pid) (fun plbl ->
          let acode0 = layout_procedure cf cid pid plbl code1 in
          ret state_monad0 (PMap.add pid acode0 res_map)))
    in layout_procedures
  in
  let aux =
    let rec aux = function
    | [] -> ret state_monad0 PMap.empty
    | y :: xs ->
      let (cid, procs_map) = y in
      bind0 state_monad0 (Obj.magic CompStateMonad.get) (fun _ ->
        bind0 state_monad0 (aux xs) (fun res_map ->
          bind0 state_monad0
            (layout_procedures cid (PMap.elements procs_map))
            (fun proc_res -> ret state_monad0 (PMap.add cid proc_res res_map))))
    in aux
  in
  bind0 (Obj.magic state_monad0) (Obj.magic aux (PMap.elements acode))
    check_labeled_code

(** val index_of : label0 -> lcode -> int **)

let index_of lbl listing =
  fst
    (fold_left (fun pat0 pat ->
      let (index, found) = pat0 in
      let (crt_lbls, _) = pat in
      if eqb0 found false
      then (match crt_lbls with
            | Some llst ->
              if existsb (label_eqb lbl) llst
              then (index, true)
              else ((add index (Pervasives.succ 0)), false)
            | None -> ((add index (Pervasives.succ 0)), false))
      else (index, found)) listing (0, false))

(** val get_E :
    lcode PMap.t PMap.t -> (compiler_env, Env.coq_E) CompStateMonad.t **)

let get_E lcode0 =
  let fold_procs =
    let rec fold_procs cid procs_lst acc =
      bind0 state_monad0 (Obj.magic CompStateMonad.get) (fun _ ->
        match procs_lst with
        | [] -> ret state_monad0 acc
        | y :: xs ->
          let (pid, lbl) = y in
          (match PMap.find cid lcode0 with
           | Some procs_lmap ->
             (match PMap.find pid procs_lmap with
              | Some listing ->
                let i = index_of lbl listing in
                if Coq_Nat.ltb i (length listing)
                then bind0 state_monad0
                       (Obj.magic get_SFI_code_address cid pid i)
                       (fun address0 ->
                       fold_procs cid xs ((address0,
                         (Coq_Pos.to_nat pid)) :: acc))
                else CompStateMonad.fail
                       ('g'::('e'::('t'::('_'::('E'::(' '::('t'::('h'::('e'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::('e'::('x'::('p'::('o'::('r'::('t'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('i'::('s'::(' '::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('i'::('n'::(' '::('t'::('h'::('e'::(' '::('l'::('i'::('s'::('t'::('i'::('n'::('g'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                       (TwoPosArg (cid, pid))
              | None ->
                CompStateMonad.fail
                  ('g'::('e'::('t'::('_'::('E'::(' '::('d'::('i'::('d'::(' '::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::(' '::('i'::('n'::(' '::('l'::('c'::('o'::('d'::('e'::[])))))))))))))))))))))))))))))))))))))
                  (TwoPosArg (cid, pid)))
           | None ->
             CompStateMonad.fail
               ('g'::('e'::('t'::('_'::('E'::(' '::('d'::('i'::('d'::(' '::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::(' '::('i'::('n'::(' '::('l'::('c'::('o'::('d'::('e'::[])))))))))))))))))))))))))))))))))))))
               (PosArg cid)))
    in fold_procs
  in
  let fold_comp =
    let rec fold_comp clist acc =
      match clist with
      | [] -> ret state_monad0 acc
      | p :: xs ->
        let (cid, pmap) = p in
        bind0 state_monad0 (fold_procs cid (PMap.elements pmap) [])
          (fun res -> fold_comp xs (app acc res))
    in fold_comp
  in
  bind0 (Obj.magic state_monad0) (Obj.magic CompStateMonad.get) (fun cenv ->
    Obj.magic fold_comp (PMap.elements cenv.exported_procedures_labels) [])

(** val label2address :
    lcode PMap.t PMap.t -> (compiler_env, (label0 * RiscMachine.address) list
    PMap.t PMap.t) CompStateMonad.t **)

let label2address lc =
  let fold_instr =
    let rec fold_instr cid pid list_instr acc =
      match list_instr with
      | [] -> ret state_monad0 acc
      | y :: xs ->
        let (i, y0) = y in
        let (y1, _) = y0 in
        (match y1 with
         | Some lbls ->
           bind0 state_monad0 (Obj.magic get_SFI_code_address cid pid i)
             (fun address0 ->
             fold_instr cid pid xs
               (app acc (combine lbls (repeat address0 (length lbls)))))
         | None -> fold_instr cid pid xs acc)
    in fold_instr
  in
  let fold_procs =
    let rec fold_procs cid procs_lst acc =
      bind0 state_monad0 (Obj.magic CompStateMonad.get) (fun _ ->
        match procs_lst with
        | [] -> ret state_monad0 acc
        | y :: xs ->
          let (pid, proc_lcode) = y in
          bind0 state_monad0
            (fold_instr cid pid
              (combine (seq 0 (length proc_lcode)) proc_lcode) [])
            (fun res -> fold_procs cid xs (PMap.add pid res acc)))
    in fold_procs
  in
  let fold_comp =
    let rec fold_comp clist acc =
      match clist with
      | [] -> ret state_monad0 acc
      | p :: xs ->
        let (cid, pmap) = p in
        bind0 state_monad0 (fold_procs cid (PMap.elements pmap) PMap.empty)
          (fun res -> fold_comp xs (PMap.add cid res acc))
    in fold_comp
  in
  Obj.magic fold_comp (PMap.elements lc) PMap.empty

(** val get_address :
    component_id -> procedure_id -> label0 -> (label0 * RiscMachine.address)
    list PMap.t PMap.t -> (compiler_env, RiscMachine.address) CompStateMonad.t **)

let get_address cid pid lbl l2a =
  bind0 (Obj.magic state_monad0)
    (CompStateMonad.lift (PMap.find cid (Obj.magic l2a))
      ('g'::('e'::('t'::('_'::('a'::('d'::('d'::('r'::('e'::('s'::('s'::(':'::('N'::('o'::(' '::('c'::('i'::('d'::[]))))))))))))))))))
      (PosArg cid)) (fun pmap ->
    bind0 (Obj.magic state_monad0)
      (CompStateMonad.lift (PMap.find pid pmap)
        ('g'::('e'::('t'::('_'::('a'::('d'::('d'::('r'::('e'::('s'::('s'::(':'::('N'::('o'::(' '::('p'::('i'::('d'::[]))))))))))))))))))
        (TwoPosArg (cid, pid))) (fun pl ->
      match find (fun pat -> let (l, _) = pat in label_eqb l lbl) pl with
      | Some p -> let (_, a) = p in ret (Obj.magic state_monad0) a
      | None ->
        CompStateMonad.fail
          ('g'::('e'::('t'::('_'::('a'::('d'::('d'::('r'::('e'::('s'::('s'::(':'::('A'::('d'::('d'::('r'::('e'::('s'::('s'::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::[])))))))))))))))))))))))))))))
          NoInfo))

(** val get_address_by_label :
    label0 -> (label0 * RiscMachine.address) list PMap.t PMap.t ->
    (compiler_env, RiscMachine.address) CompStateMonad.t **)

let get_address_by_label lbl l2a =
  let ll =
    concat
      (flat_map (fun pmap -> map snd (PMap.elements pmap))
        (map snd (PMap.elements l2a)))
  in
  (match find (fun pat -> let (l, _) = pat in label_eqb l lbl) ll with
   | Some p -> let (_, a) = p in ret (Obj.magic state_monad0) a
   | None ->
     CompStateMonad.fail
       ('g'::('e'::('t'::('_'::('a'::('d'::('d'::('r'::('e'::('s'::('s'::('_'::('b'::('y'::('_'::('l'::('a'::('b'::('e'::('l'::[]))))))))))))))))))))
       NoInfo)

(** val generate_comp0_memory :
    component_id -> procedure_id -> RiscMachine.Memory.t ->
    (label0 * RiscMachine.address) list PMap.t PMap.t -> (compiler_env,
    RiscMachine.Memory.t) CompStateMonad.t **)

let generate_comp0_memory mcid mpid mem1 l2a =
  bind0 (Obj.magic state_monad0) (Obj.magic get_proc_label mcid mpid)
    (fun main_label ->
    bind0 (Obj.magic state_monad0)
      (Obj.magic get_address mcid mpid main_label l2a) (fun main_address ->
      let mem2 =
        RiscMachine.Memory.set_instr mem1
          (SFI.address_of SFI.coq_MONITOR_COMPONENT_ID 0 0)
          (RiscMachine.ISA.IConst (0, RiscMachine.Register.coq_R_SFI_SP))
      in
      let mem3 =
        RiscMachine.Memory.set_instr mem2
          (SFI.address_of SFI.coq_MONITOR_COMPONENT_ID 0 1)
          (RiscMachine.ISA.IConst
          ((RiscMachine.to_value SFI.coq_AND_DATA_MASK),
          RiscMachine.Register.coq_R_AND_DATA_MASK))
      in
      let mem4 =
        RiscMachine.Memory.set_instr mem3
          (SFI.address_of SFI.coq_MONITOR_COMPONENT_ID 0 ((fun p->2*p) 1))
          (RiscMachine.ISA.IConst
          ((RiscMachine.to_value SFI.coq_AND_CODE_MASK),
          RiscMachine.Register.coq_R_AND_CODE_MASK))
      in
      let mem5 =
        RiscMachine.Memory.set_instr mem4
          (SFI.address_of SFI.coq_MONITOR_COMPONENT_ID 0 ((fun p->1+2*p) 1))
          (RiscMachine.ISA.IConst (1, RiscMachine.Register.coq_R_ONE))
      in
      let mem6 =
        RiscMachine.Memory.set_instr mem5
          (SFI.address_of SFI.coq_MONITOR_COMPONENT_ID 0 ((fun p->2*p)
            ((fun p->2*p) 1))) (RiscMachine.ISA.IJal main_address)
      in
      ret (Obj.magic state_monad0)
        (RiscMachine.Memory.set_instr mem6
          (SFI.address_of SFI.coq_MONITOR_COMPONENT_ID 0 ((fun p->1+2*p)
            ((fun p->2*p) 1))) RiscMachine.ISA.IHalt)))

(** val generate_instruction :
    component_id -> procedure_id -> (label0 list option * ainstr) ->
    (label0 * RiscMachine.address) list PMap.t PMap.t -> int ->
    RiscMachine.Memory.t -> (compiler_env, RiscMachine.Memory.t)
    CompStateMonad.t **)

let generate_instruction cid pid li l2a offset0 mem1 =
  bind0 (Obj.magic state_monad0)
    (Obj.magic get_SFI_code_address cid pid offset0) (fun address0 ->
    let (_, i) = li in
    (match i with
     | INop0 ->
       ret (Obj.magic state_monad0)
         (RiscMachine.Memory.set_instr mem1 address0 RiscMachine.ISA.INop)
     | ILabel0 _ ->
       CompStateMonad.fail
         ('g'::('e'::('n'::('e'::('r'::('a'::('t'::('e'::('_'::('i'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))
         NoInfo
     | IConst0 (v, r) ->
       ret (Obj.magic state_monad0)
         (RiscMachine.Memory.set_instr mem1 address0 (RiscMachine.ISA.IConst
           (v, r)))
     | IMov0 (r1, r2) ->
       ret (Obj.magic state_monad0)
         (RiscMachine.Memory.set_instr mem1 address0 (RiscMachine.ISA.IMov
           (r1, r2)))
     | IBinOp0 (op0, r1, r2, r3) ->
       ret (Obj.magic state_monad0)
         (RiscMachine.Memory.set_instr mem1 address0 (RiscMachine.ISA.IBinOp
           (op0, r1, r2, r3)))
     | ILoad0 (r1, r2) ->
       ret (Obj.magic state_monad0)
         (RiscMachine.Memory.set_instr mem1 address0 (RiscMachine.ISA.ILoad
           (r1, r2)))
     | IStore0 (r1, r2) ->
       ret (Obj.magic state_monad0)
         (RiscMachine.Memory.set_instr mem1 address0 (RiscMachine.ISA.IStore
           (r1, r2)))
     | IBnz0 (r, lbl) ->
       bind0 (Obj.magic state_monad0) (Obj.magic get_address cid pid lbl l2a)
         (fun target_address ->
         let branch_offset = Z.sub (Z.of_N target_address) (Z.of_N address0)
         in
         ret (Obj.magic state_monad0)
           (RiscMachine.Memory.set_instr mem1 address0 (RiscMachine.ISA.IBnz
             (r, branch_offset))))
     | IJump0 r ->
       ret (Obj.magic state_monad0)
         (RiscMachine.Memory.set_instr mem1 address0 (RiscMachine.ISA.IJump
           r))
     | IJal0 lbl ->
       bind0 (Obj.magic state_monad0)
         (Obj.magic get_address_by_label lbl l2a) (fun new_address ->
         ret (Obj.magic state_monad0)
           (RiscMachine.Memory.set_instr mem1 address0 (RiscMachine.ISA.IJal
             new_address)))
     | IHalt0 ->
       ret (Obj.magic state_monad0)
         (RiscMachine.Memory.set_instr mem1 address0 RiscMachine.ISA.IHalt)))

(** val generate_procedure_code :
    component_id -> procedure_id -> lcode -> (label0 * RiscMachine.address)
    list PMap.t PMap.t -> RiscMachine.Memory.t -> (compiler_env,
    RiscMachine.Memory.t) CompStateMonad.t **)

let generate_procedure_code cid pid linstrs l2a mem1 =
  let aux =
    let rec aux lst acc = match acc with
    | (index, mem2) ->
      (match lst with
       | [] -> ret state_monad0 acc
       | i :: xs ->
         bind0 state_monad0
           (Obj.magic generate_instruction cid pid i l2a index mem2)
           (fun res -> aux xs ((add index (Pervasives.succ 0)), res)))
    in aux
  in
  bind0 (Obj.magic state_monad0) (Obj.magic aux linstrs (0, mem1))
    (fun res -> ret (Obj.magic state_monad0) (snd res))

(** val generate_component_code :
    component_id -> lcode PMap.t -> (label0 * RiscMachine.address) list
    PMap.t PMap.t -> RiscMachine.Memory.t -> (compiler_env,
    RiscMachine.Memory.t) CompStateMonad.t **)

let generate_component_code cid pmap l2a mem1 =
  let aux =
    let rec aux lst acc =
      match lst with
      | [] -> ret state_monad0 acc
      | p :: xs ->
        let (pid, linstrs) = p in
        bind0 state_monad0
          (Obj.magic generate_procedure_code cid pid linstrs l2a acc)
          (fun res -> aux xs res)
    in aux
  in
  Obj.magic aux (PMap.elements pmap) mem1

(** val generate_code_memory :
    lcode PMap.t PMap.t -> (label0 * RiscMachine.address) list PMap.t PMap.t
    -> RiscMachine.Memory.t -> (compiler_env, RiscMachine.Memory.t)
    CompStateMonad.t **)

let generate_code_memory labeled_code l2a mem1 =
  let aux =
    let rec aux lst acc =
      match lst with
      | [] -> ret state_monad0 acc
      | y :: xs ->
        let (cid, pmap) = y in
        bind0 state_monad0
          (Obj.magic generate_component_code cid pmap l2a acc) (fun res ->
          aux xs res)
    in aux
  in
  Obj.magic aux (PMap.elements labeled_code) mem1

(** val convert_prog_interface : Program.interface -> prog_int **)

let convert_prog_interface pi =
  fold_left (fun acc pat ->
    let (cid, cint) = pat in
    PMap.add (Coq_Pos.of_nat cid)
      ((map (Obj.magic Coq_Pos.of_nat)
         ((fset_of_subType nat_ordType).val0
           (Obj.magic Component.export cint))),
      (map (fun pat0 ->
        let (c, p) = Obj.magic pat0 in
        ((Coq_Pos.of_nat c), (Coq_Pos.of_nat p)))
        ((fset_of_subType (prod_ordType nat_ordType nat_ordType)).val0
          (Obj.magic Component.import cint)))) acc) (elementsm pi) PMap.empty

(** val convert_prog_buffers :
    (Block.id * (int, value list) sum) list nMap ->
    (component_id * (block_id * (int, value list) sum) list) list **)

let convert_prog_buffers buffers =
  fold_left (fun acc pat ->
    let (cid, l) = pat in
    ((Coq_Pos.of_nat cid),
    (map (fun pat0 -> let (bid, s) = pat0 in ((Coq_Pos.of_nat bid), s)) l)) :: acc)
    (elementsm buffers) []

(** val convert_prog_procs : code nMap nMap -> code PMap.t PMap.t **)

let convert_prog_procs procs =
  fold_left (fun acc1 pat ->
    let (cid, pmap) = pat in
    PMap.add (Coq_Pos.of_nat cid)
      (fold_left (fun acc2 pat0 ->
        let (pid, c) = pat0 in PMap.add (Coq_Pos.of_nat pid) c acc2)
        (elementsm pmap) PMap.empty) acc1) (elementsm procs) PMap.empty

(** val compile_program :
    comp_flags -> Intermediate.program -> sfi_program compEither **)

let compile_program cf ip =
  let cip = convert_prog_interface ip.Intermediate.prog_interface in
  let buffs = convert_prog_buffers ip.Intermediate.prog_buffers in
  let pr_progs = convert_prog_procs ip.Intermediate.prog_procedures in
  let cn0 = gen_cn cip in
  let cid2SFIid0 =
    fold_left (fun acc pat ->
      let (cid, i) = pat in PMap.add cid (Env.index2SFIid i) acc)
      (combine cn0 (seq 0 (length cn0))) PMap.empty
  in
  let procs_labels = exported_procs_labels pr_progs cip in
  let max_label0 =
    fold_left N.max
      (flat_map (fun m ->
        map (fun pat -> let (_, y0) = pat in let (_, l) = y0 in l)
          (PMap.elements m)) (map snd (PMap.elements procs_labels))) 1
  in
  let procId2slot0 = allocate_procedure_slots pr_progs in
  CompStateMonad.run
    (init_env cf cid2SFIid0 procId2slot0 procs_labels (N.add max_label0 1))
    (bind0 (Obj.magic state_monad0) (Obj.magic allocate_buffers buffs)
      (fun data_mem' ->
      bind0 (Obj.magic state_monad0) (Obj.magic init_buffers data_mem' buffs)
        (fun data_mem ->
        bind0 (Obj.magic state_monad0)
          (Obj.magic compile_components (PMap.elements pr_progs) cip)
          (fun acode ->
          bind0 (Obj.magic state_monad0)
            (Obj.magic layout_code cf (PMapExtra.of_list acode))
            (fun labeled_code ->
            bind0 (Obj.magic state_monad0) (Obj.magic get_E labeled_code)
              (fun e1 ->
              bind0 (Obj.magic state_monad0)
                (Obj.magic label2address labeled_code) (fun l2a ->
                match ip.Intermediate.prog_main with
                | Some p ->
                  let (cid, pid) = p in
                  bind0 (Obj.magic state_monad0)
                    (Obj.magic generate_comp0_memory (Coq_Pos.of_nat cid)
                      (Coq_Pos.of_nat pid) data_mem l2a) (fun mem1 ->
                    bind0 (Obj.magic state_monad0)
                      (Obj.magic generate_code_memory labeled_code l2a mem1)
                      (fun mem2 ->
                      ret (Obj.magic state_monad0) { cn =
                        (map Coq_Pos.to_nat cn0); e = e1; mem0 = mem2;
                        prog_interface0 = ip.Intermediate.prog_interface }))
                | None ->
                  CompStateMonad.fail
                    ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('m'::('a'::('i'::('n'::[]))))))))))))
                    NoInfo)))))))

type executionError =
| RegisterNotFound of MachineState.t * RiscMachine.Register.t
| NoInfo0
| UninitializedMemory of MachineState.t * RiscMachine.address
| CodeMemoryException of MachineState.t * RiscMachine.address
   * RiscMachine.ISA.instr
| DataMemoryException of MachineState.t * RiscMachine.address
   * RiscMachine.value
| MissingComponentId of MachineState.t * SFIComponent.id * Env.coq_CN
| CallEventError of MachineState.t * SFIComponent.id * SFIComponent.id
   * Env.coq_CN * Env.coq_E
| RetEventError of MachineState.t * SFIComponent.id * SFIComponent.id
   * Env.coq_CN
| IllegalJalToZeroComponent of MachineState.t
| IllegalJumpFromZeroComponent of MachineState.t

type 'a either =
| Right0 of 'a
| Left0 of char list * executionError

module StateMonad =
 struct
  type ('st, 'res) t = 'st -> 'res either * 'st

  (** val ret : 'a2 -> ('a1, 'a2) t **)

  let ret x s =
    ((Right0 x), s)

  (** val bind :
      ('a1, 'a2) t -> ('a2 -> ('a1, 'a3) t) -> 'a1 -> 'a3 either * 'a1 **)

  let bind s f x =
    let (e1, s') = s x in
    (match e1 with
     | Right0 x' -> f x' s'
     | Left0 (msg, err) -> ((Left0 (msg, err)), s'))

  (** val modify : ('a1 -> 'a1) -> ('a1, unit) t **)

  let modify f s =
    ((Right0 ()), (f s))

  (** val lift : 'a2 option -> char list -> executionError -> ('a1, 'a2) t **)

  let lift x msg err s =
    match x with
    | Some v -> ((Right0 v), s)
    | None -> ((Left0 (msg, err)), s)

  (** val fail : char list -> executionError -> ('a1, 'a2) t **)

  let fail msg err s =
    ((Left0 (msg, err)), s)
 end

(** val state_monad1 : ('a1, __) StateMonad.t monad **)

let state_monad1 =
  { ret = (fun _ -> StateMonad.ret); bind0 = (fun _ _ -> StateMonad.bind) }

module CS =
 struct
  (** val call_trace :
      Env.t -> RiscMachine.pc -> RiscMachine.pc -> RiscMachine.RegisterFile.t
      -> trace option **)

  let call_trace g pc0 pc' gen_regs =
    bind0 (Obj.magic option_monad)
      (Obj.magic RiscMachine.RegisterFile.get_register
        RiscMachine.Register.coq_R_COM gen_regs) (fun rcomval ->
      bind0 (Obj.magic option_monad)
        (Obj.magic Env.get_component_name_from_id (SFI.coq_C_SFI pc0) g)
        (fun cpc ->
        bind0 (Obj.magic option_monad)
          (Obj.magic Env.get_component_name_from_id (SFI.coq_C_SFI pc') g)
          (fun cpc' ->
          bind0 (Obj.magic option_monad) (Obj.magic Env.get_procedure pc' g)
            (fun p -> Some ((ECall (cpc, p, rcomval, cpc')) :: [])))))

  (** val coq_DEBUG : bool **)

  let coq_DEBUG =
    false

  (** val eval_step_with_state :
      Env.t -> MachineState.t -> ('a1, trace * MachineState.t) StateMonad.t **)

  let eval_step_with_state g s = match s with
  | (p, gen_regs) ->
    let (mem1, pc0) = p in
    let get_reg = fun r ->
      StateMonad.lift (RiscMachine.RegisterFile.get_register r gen_regs)
        ('U'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[]))))))))))))))))
        (RegisterNotFound (s, r))
    in
    (match RiscMachine.Memory.get_word mem1 pc0 with
     | Some w ->
       (match w with
        | RiscMachine.Data val1 ->
          StateMonad.fail
            ('P'::('c'::(' '::('i'::('n'::(' '::('d'::('a'::('t'::('a'::(' '::('m'::('e'::('m'::('o'::('r'::('y'::[])))))))))))))))))
            (DataMemoryException (s, pc0, val1))
        | RiscMachine.Instruction instr0 ->
          (match instr0 with
           | RiscMachine.ISA.INop ->
             ret (Obj.magic state_monad) (Right0 (e0, ((mem1,
               (RiscMachine.inc_pc pc0)), gen_regs)))
           | RiscMachine.ISA.IConst (val1, reg) ->
             let gen_regs' =
               RiscMachine.RegisterFile.set_register reg val1 gen_regs
             in
             ret (Obj.magic state_monad1) (e0, ((mem1,
               (RiscMachine.inc_pc pc0)), gen_regs'))
           | RiscMachine.ISA.IMov (reg_src, reg_dst) ->
             bind0 (Obj.magic state_monad1) (Obj.magic get_reg reg_src)
               (fun val1 ->
               let gen_regs' =
                 RiscMachine.RegisterFile.set_register reg_dst val1 gen_regs
               in
               ret (Obj.magic state_monad1) (e0, ((mem1,
                 (RiscMachine.inc_pc pc0)), gen_regs')))
           | RiscMachine.ISA.IBinOp (op0, reg_src1, reg_src2, reg_dst) ->
             bind0 (Obj.magic state_monad1) (Obj.magic get_reg reg_src1)
               (fun val1 ->
               bind0 (Obj.magic state_monad1) (Obj.magic get_reg reg_src2)
                 (fun val2 ->
                 let result1 = RiscMachine.eval_binop op0 val1 val2 in
                 let gen_regs' =
                   RiscMachine.RegisterFile.set_register reg_dst result1
                     gen_regs
                 in
                 ret (Obj.magic state_monad1) (e0, ((mem1,
                   (RiscMachine.inc_pc pc0)), gen_regs'))))
           | RiscMachine.ISA.ILoad (rptr, rd) ->
             bind0 (Obj.magic state_monad1) (Obj.magic get_reg rptr)
               (fun ptr ->
               if coq_DEBUG
               then let addr = RiscMachine.Memory.to_address ptr in
                    bind0 (Obj.magic state_monad1)
                      (StateMonad.lift
                        (Obj.magic RiscMachine.Memory.get_word mem1 addr)
                        ('U'::('n'::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('d'::(' '::('m'::('e'::('m'::('('::('I'::('L'::('o'::('a'::('d'::(')'::(' '::[])))))))))))))))))))))))))
                        (UninitializedMemory (s, addr))) (fun word0 ->
                      match word0 with
                      | RiscMachine.Data val1 ->
                        let gen_regs' =
                          RiscMachine.RegisterFile.set_register rd val1
                            gen_regs
                        in
                        ret (Obj.magic state_monad1) (e0, ((mem1,
                          (RiscMachine.inc_pc pc0)), gen_regs'))
                      | RiscMachine.Instruction i ->
                        StateMonad.fail
                          ('I'::('L'::('o'::('a'::('d'::(' '::('f'::('r'::('o'::('m'::(' '::('c'::('o'::('d'::('e'::(' '::('m'::('e'::('m'::('o'::('r'::('y'::(' '::[])))))))))))))))))))))))
                          (CodeMemoryException (s, addr, i)))
               else let addr = RiscMachine.Memory.to_address ptr in
                    let val1 =
                      match RiscMachine.Memory.get_word mem1 addr with
                      | Some word0 ->
                        (match word0 with
                         | RiscMachine.Data val1 -> val1
                         | RiscMachine.Instruction _ -> 0)
                      | None -> 0
                    in
                    let gen_regs' =
                      RiscMachine.RegisterFile.set_register rd val1 gen_regs
                    in
                    ret (Obj.magic state_monad1) (e0, ((mem1,
                      (RiscMachine.inc_pc pc0)), gen_regs')))
           | RiscMachine.ISA.IStore (rptr, rs) ->
             bind0 (Obj.magic state_monad1) (Obj.magic get_reg rptr)
               (fun ptr ->
               let addr = RiscMachine.Memory.to_address ptr in
               if SFI.is_code_address addr
               then StateMonad.fail
                      ('I'::('S'::('t'::('o'::('r'::('e'::(' '::('i'::('n'::(' '::('c'::('o'::('d'::('e'::(' '::('m'::('e'::('m'::('o'::('r'::('y'::[])))))))))))))))))))))
                      (CodeMemoryException (s, addr, instr0))
               else bind0 (Obj.magic state_monad1) (Obj.magic get_reg rs)
                      (fun val1 ->
                      let mem' = RiscMachine.Memory.set_value mem1 addr val1
                      in
                      ret (Obj.magic state_monad1) (e0, ((mem',
                        (RiscMachine.inc_pc pc0)), gen_regs))))
           | RiscMachine.ISA.IBnz (reg, offset0) ->
             bind0 (Obj.magic state_monad1) (Obj.magic get_reg reg)
               (fun val1 ->
               let pc' =
                 if Z.eqb val1 0
                 then RiscMachine.inc_pc pc0
                 else Z.to_N (Z.add (Z.of_N pc0) offset0)
               in
               ret (Obj.magic state_monad1) (e0, ((mem1, pc'), gen_regs)))
           | RiscMachine.ISA.IJump reg ->
             bind0 (Obj.magic state_monad1) (Obj.magic get_reg reg)
               (fun addr ->
               let pc' = RiscMachine.Memory.to_address addr in
               if SFI.is_same_component_bool pc0 pc'
               then ret (Obj.magic state_monad1) (e0, ((mem1, pc'), gen_regs))
               else if N.eqb (SFI.coq_C_SFI pc') SFI.coq_MONITOR_COMPONENT_ID
                    then ret (Obj.magic state_monad1) (e0, ((mem1, pc'),
                           gen_regs))
                    else bind0 (Obj.magic state_monad1)
                           (Obj.magic get_reg RiscMachine.Register.coq_R_COM)
                           (fun rcomval ->
                           bind0 (Obj.magic state_monad1)
                             (StateMonad.lift
                               (Obj.magic Env.get_component_name_from_id
                                 (SFI.coq_C_SFI pc0) g)
                               ('N'::('o'::(' '::('i'::('n'::('t'::('e'::('r'::('m'::('e'::('d'::('i'::('a'::('t'::('e'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::(' '::('i'::('d'::[]))))))))))))))))))))))))))))
                               (MissingComponentId (s, (SFI.coq_C_SFI pc0),
                               (fst g)))) (fun cpc ->
                             bind0 (Obj.magic state_monad1)
                               (StateMonad.lift
                                 (Obj.magic Env.get_component_name_from_id
                                   (SFI.coq_C_SFI pc') g)
                                 ('N'::('o'::(' '::('i'::('n'::('t'::('e'::('r'::('m'::('e'::('d'::('i'::('a'::('t'::('e'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::(' '::('i'::('d'::[]))))))))))))))))))))))))))))
                                 (MissingComponentId (s, (SFI.coq_C_SFI pc'),
                                 (fst g)))) (fun cpc' ->
                               ret (Obj.magic state_monad1) (((ERet (cpc,
                                 rcomval, cpc')) :: []), ((mem1, pc'),
                                 gen_regs))))))
           | RiscMachine.ISA.IJal addr ->
             let ra = Z.of_N (N.add pc0 1) in
             let gen_regs' =
               RiscMachine.RegisterFile.set_register
                 RiscMachine.Register.coq_R_RA ra gen_regs
             in
             if SFI.is_same_component_bool pc0 addr
             then ret (Obj.magic state_monad1) (e0, ((mem1, addr), gen_regs'))
             else if N.eqb (SFI.coq_C_SFI pc0) SFI.coq_MONITOR_COMPONENT_ID
                  then ret (Obj.magic state_monad1) (e0, ((mem1, addr),
                         gen_regs'))
                  else let ot = call_trace g pc0 addr gen_regs in
                       (match ot with
                        | Some t1 ->
                          ret (Obj.magic state_monad1) (t1, ((mem1, addr),
                            gen_regs'))
                        | None ->
                          StateMonad.fail
                            ('C'::('a'::('l'::('l'::(' '::('t'::('r'::('a'::('c'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::[]))))))))))))))))
                            (CallEventError (s, (SFI.coq_C_SFI pc0),
                            (SFI.coq_C_SFI addr), (fst g), (snd g))))
           | RiscMachine.ISA.IHalt ->
             ret (Obj.magic state_monad1) (e0, ((mem1, pc0), gen_regs))))
     | None ->
       if coq_DEBUG
       then StateMonad.fail
              ('P'::('c'::(' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::(' '::('n'::('o'::('t'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('d'::[]))))))))))))))))))))))))))
              (UninitializedMemory (s, pc0))
       else if SFI.last_address_in_slot pc0
            then ret (Obj.magic state_monad1) (e0,
                   (((RiscMachine.Memory.set_instr mem1 pc0
                       RiscMachine.ISA.IHalt), pc0), gen_regs))
            else ret (Obj.magic state_monad1) (e0, ((mem1,
                   (RiscMachine.inc_pc pc0)), gen_regs)))

  (** val eval_steps_with_state :
      (Env.t -> MachineState.t -> trace -> MachineState.t -> 'a1 -> 'a1) ->
      int -> Env.t -> MachineState.t -> ('a1, (trace * MachineState.t) * int)
      StateMonad.t **)

  let rec eval_steps_with_state update_state_records n g s =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> ret (Obj.magic state_monad1) ((e0, s), 0))
      (fun n' ->
      bind0 (Obj.magic state_monad1) (Obj.magic eval_step_with_state g s)
        (fun x ->
        let (t', s') = x in
        bind0 (Obj.magic state_monad1)
          (Obj.magic StateMonad.modify (update_state_records g s t' s'))
          (fun _ ->
          let (p, _) = s in
          let (mem1, pc0) = p in
          (match RiscMachine.Memory.get_word mem1 pc0 with
           | Some w ->
             (match w with
              | RiscMachine.Data _ ->
                if coq_DEBUG
                then StateMonad.fail
                       ('e'::('v'::('a'::('l'::('_'::('s'::('t'::('e'::('p'::('s'::('_'::('w'::('i'::('t'::('h'::('_'::('s'::('t'::('a'::('t'::('e'::(':'::(' '::('I'::('m'::('p'::('o'::('s'::('s'::('i'::('b'::('l'::('e'::(' '::('b'::('r'::('a'::('n'::('c'::('h'::[]))))))))))))))))))))))))))))))))))))))))
                       NoInfo0
                else bind0 (Obj.magic state_monad1)
                       (eval_steps_with_state update_state_records n' g s')
                       (fun x0 ->
                       let (p0, n'') = x0 in
                       let (t'', s'') = p0 in
                       ret (Obj.magic state_monad1) (((app t' t''), s''), n''))
              | RiscMachine.Instruction instr0 ->
                (match instr0 with
                 | RiscMachine.ISA.INop ->
                   bind0 (Obj.magic state_monad1)
                     (eval_steps_with_state update_state_records n' g s')
                     (fun x0 ->
                     let (p0, n'') = x0 in
                     let (t'', s'') = p0 in
                     ret (Obj.magic state_monad1) (((app t' t''), s''), n''))
                 | RiscMachine.ISA.IConst (_, _) ->
                   bind0 (Obj.magic state_monad1)
                     (eval_steps_with_state update_state_records n' g s')
                     (fun x0 ->
                     let (p0, n'') = x0 in
                     let (t'', s'') = p0 in
                     ret (Obj.magic state_monad1) (((app t' t''), s''), n''))
                 | RiscMachine.ISA.IMov (_, _) ->
                   bind0 (Obj.magic state_monad1)
                     (eval_steps_with_state update_state_records n' g s')
                     (fun x0 ->
                     let (p0, n'') = x0 in
                     let (t'', s'') = p0 in
                     ret (Obj.magic state_monad1) (((app t' t''), s''), n''))
                 | RiscMachine.ISA.IBinOp (_, _, _, _) ->
                   bind0 (Obj.magic state_monad1)
                     (eval_steps_with_state update_state_records n' g s')
                     (fun x0 ->
                     let (p0, n'') = x0 in
                     let (t'', s'') = p0 in
                     ret (Obj.magic state_monad1) (((app t' t''), s''), n''))
                 | RiscMachine.ISA.ILoad (_, _) ->
                   bind0 (Obj.magic state_monad1)
                     (eval_steps_with_state update_state_records n' g s')
                     (fun x0 ->
                     let (p0, n'') = x0 in
                     let (t'', s'') = p0 in
                     ret (Obj.magic state_monad1) (((app t' t''), s''), n''))
                 | RiscMachine.ISA.IStore (_, _) ->
                   bind0 (Obj.magic state_monad1)
                     (eval_steps_with_state update_state_records n' g s')
                     (fun x0 ->
                     let (p0, n'') = x0 in
                     let (t'', s'') = p0 in
                     ret (Obj.magic state_monad1) (((app t' t''), s''), n''))
                 | RiscMachine.ISA.IBnz (_, _) ->
                   bind0 (Obj.magic state_monad1)
                     (eval_steps_with_state update_state_records n' g s')
                     (fun x0 ->
                     let (p0, n'') = x0 in
                     let (t'', s'') = p0 in
                     ret (Obj.magic state_monad1) (((app t' t''), s''), n''))
                 | RiscMachine.ISA.IJump _ ->
                   bind0 (Obj.magic state_monad1)
                     (eval_steps_with_state update_state_records n' g s')
                     (fun x0 ->
                     let (p0, n'') = x0 in
                     let (t'', s'') = p0 in
                     ret (Obj.magic state_monad1) (((app t' t''), s''), n''))
                 | RiscMachine.ISA.IJal _ ->
                   bind0 (Obj.magic state_monad1)
                     (eval_steps_with_state update_state_records n' g s')
                     (fun x0 ->
                     let (p0, n'') = x0 in
                     let (t'', s'') = p0 in
                     ret (Obj.magic state_monad1) (((app t' t''), s''), n''))
                 | RiscMachine.ISA.IHalt ->
                   ret (Obj.magic state_monad1) ((t', s'), n')))
           | None ->
             if coq_DEBUG
             then StateMonad.fail
                    ('e'::('v'::('a'::('l'::('_'::('s'::('t'::('e'::('p'::('s'::('_'::('w'::('i'::('t'::('h'::('_'::('s'::('t'::('a'::('t'::('e'::(':'::(' '::('I'::('m'::('p'::('o'::('s'::('s'::('i'::('b'::('l'::('e'::(' '::('b'::('r'::('a'::('n'::('c'::('h'::[]))))))))))))))))))))))))))))))))))))))))
                    NoInfo0
             else bind0 (Obj.magic state_monad1)
                    (eval_steps_with_state update_state_records n' g s')
                    (fun x0 ->
                    let (p0, n'') = x0 in
                    let (t'', s'') = p0 in
                    ret (Obj.magic state_monad1) (((app t' t''), s''), n''))))))
      n

  (** val eval_program_with_state :
      (Env.t -> MachineState.t -> trace -> MachineState.t -> 'a1 -> 'a1) ->
      int -> sfi_program -> RiscMachine.RegisterFile.t -> ('a1,
      (trace * MachineState.t) * int) StateMonad.t **)

  let eval_program_with_state update_state_records fuel p regs =
    let st0 = ((p.mem0, RiscMachine.coq_PC0), regs) in
    let g = (p.cn, p.e) in
    bind0 (Obj.magic state_monad1)
      (eval_steps_with_state update_state_records fuel g st0) (fun res ->
      let (p0, n) = res in
      let (t1, s) = p0 in ret (Obj.magic state_monad1) ((t1, s), (sub fuel n)))
 end

type global_env = { genv_interface : Program.interface;
                    genv_procedures : code nMap nMap;
                    genv_entrypoints : Intermediate.EntryPoint.t }

(** val genv_interface : global_env -> Program.interface **)

let genv_interface x = x.genv_interface

(** val genv_procedures : global_env -> code nMap nMap **)

let genv_procedures x = x.genv_procedures

(** val genv_entrypoints : global_env -> Intermediate.EntryPoint.t **)

let genv_entrypoints x = x.genv_entrypoints

(** val prepare_global_env : Intermediate.program -> global_env **)

let prepare_global_env p =
  let mem1 = Intermediate.prepare_initial_memory p in
  let (p0, entrypoints) = Intermediate.prepare_procedures p mem1 in
  let (_, procs) = p0 in
  { genv_interface = p.Intermediate.prog_interface; genv_procedures = procs;
  genv_entrypoints = entrypoints }

(** val find_label : code -> label -> int option **)

let rec find_label c l =
  let rec aux c0 o =
    match c0 with
    | [] -> None
    | y :: c' ->
      (match y with
       | ILabel l' -> if (=) l l' then Some o else aux c' (Z.add 1 o)
       | _ -> aux c' (Z.add 1 o))
  in aux c 0

(** val find_label_in_procedure :
    global_env -> Pointer.t -> label -> Pointer.t option **)

let find_label_in_procedure g pc0 l =
  match getm nat_ordType g.genv_procedures (Obj.magic Pointer.component pc0) with
  | Some c_procs ->
    (match getm nat_ordType c_procs (Obj.magic Pointer.block pc0) with
     | Some p_code ->
       (match find_label p_code l with
        | Some offset0 ->
          Some (((Pointer.component pc0), (Pointer.block pc0)), offset0)
        | None -> None)
     | None -> None)
  | None -> None

(** val find_label_in_component_helper :
    global_env -> (Block.id * code) list -> Pointer.t -> label -> Pointer.t
    option **)

let rec find_label_in_component_helper g procs pc0 l =
  match procs with
  | [] -> None
  | p :: procs' ->
    let (p_block, _) = p in
    (match find_label_in_procedure g (((Pointer.component pc0), p_block), 0) l with
     | Some ptr -> Some ptr
     | None -> find_label_in_component_helper g procs' pc0 l)

(** val find_label_in_component :
    global_env -> Pointer.t -> label -> Pointer.t option **)

let find_label_in_component g pc0 l =
  match getm nat_ordType g.genv_procedures (Obj.magic Pointer.component pc0) with
  | Some c_procs -> find_label_in_component_helper g (elementsm c_procs) pc0 l
  | None -> None

module Coq_CS =
 struct
  type stack = Pointer.t list

  type state = ((stack * Memory.t) * Intermediate.Register.t) * Pointer.t

  (** val initial_machine_state : Intermediate.program -> state **)

  let initial_machine_state p =
    match p.Intermediate.prog_main with
    | Some p0 ->
      let (mainC, mainP) = p0 in
      let initial_mem = Intermediate.prepare_initial_memory p in
      let (p1, entrypoints) = Intermediate.prepare_procedures p initial_mem in
      let (mem1, _) = p1 in
      (match Intermediate.EntryPoint.get mainC mainP entrypoints with
       | Some b -> ((([], mem1), Intermediate.Register.init), ((mainC, b), 0))
       | None ->
         ((([], (emptym nat_ordType)), (emptym nat_ordType)), ((0, 0), 0)))
    | None ->
      ((([], (emptym nat_ordType)), (emptym nat_ordType)), ((0, 0), 0))
 end

type executionError0 =
| MissingComponentId0 of Pointer.t
| NegativePointerOffset of Pointer.t
| LoadOutsideComponent
| LoadNotAddressInReg
| StoreOutsideComponent
| StoreNotAddressInReg
| JumpOutsideComponent
| JumpNotAddressInReg
| MissingJalLabel
| MissingLabel
| MissingBlock of Pointer.t
| OffsetTooBig of Pointer.t
| MemoryError of Pointer.t * Pointer.t
| StoreMemoryError of Pointer.t * Pointer.t
| NotIntInReg
| AllocNegativeBlockSize
| InvalidEnv
| NoInfo1

type 'a execution_state =
| Running of 'a
| OutOfFuel of 'a
| Halted of trace
| Wrong of trace * char list * executionError0

(** val exec_monad : __ execution_state monad **)

let exec_monad =
  { ret = (fun _ x -> Running x); bind0 = (fun _ _ x f ->
    match x with
    | Running y -> f y
    | OutOfFuel y -> f y
    | x0 -> x0) }

type t0 = trace * Coq_CS.state

(** val lift0 :
    'a1 option -> char list -> executionError0 -> 'a1 execution_state **)

let lift0 x msg err =
  match x with
  | Some v -> Running v
  | None -> Wrong (e0, msg, err)

(** val fail0 : char list -> executionError0 -> 'a1 execution_state **)

let fail0 msg err =
  Wrong (e0, msg, err)

(** val eval_step : global_env -> Coq_CS.state -> t0 execution_state **)

let eval_step g = function
| (p, pc0) ->
  let (p0, regs) = p in
  let (gps, mem1) = p0 in
  bind0 (Obj.magic exec_monad)
    (lift0
      (getm nat_ordType (Obj.magic genv_procedures g)
        (Obj.magic Pointer.component pc0))
      ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::[])))))))))))))))))
      (MissingComponentId0 pc0)) (fun c_procs ->
    match getm nat_ordType c_procs (Obj.magic Pointer.block pc0) with
    | Some p_code ->
      if Z.ltb (Pointer.offset pc0) 0
      then fail0
             ('N'::('e'::('g'::('a'::('t'::('i'::('v'::('e'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::[])))))))))))))))
             (NegativePointerOffset pc0)
      else (match nth_error p_code (Z.to_nat (Pointer.offset pc0)) with
            | Some instr0 ->
              (match instr0 with
               | IConst (v, r) ->
                 let regs' = Intermediate.Register.set r (imm_to_val v) regs
                 in
                 ret (Obj.magic exec_monad) (e0, (((gps, mem1), regs'),
                   (Pointer.inc pc0)))
               | IMov (r1, r2) ->
                 let regs' =
                   Intermediate.Register.set r2
                     (Intermediate.Register.get r1 regs) regs
                 in
                 ret (Obj.magic exec_monad) (e0, (((gps, mem1), regs'),
                   (Pointer.inc pc0)))
               | IBinOp (op0, r1, r2, r3) ->
                 let regs' =
                   Intermediate.Register.set r3
                     (eval_binop op0 (Intermediate.Register.get r1 regs)
                       (Intermediate.Register.get r2 regs)) regs
                 in
                 ret (Obj.magic exec_monad) (e0, (((gps, mem1), regs'),
                   (Pointer.inc pc0)))
               | ILoad (r1, r2) ->
                 (match Intermediate.Register.get r1 regs with
                  | Ptr ptr ->
                    if Component.eqb (Pointer.component ptr)
                         (Pointer.component pc0)
                    then bind0 (Obj.magic exec_monad)
                           (lift0 (Obj.magic Memory.load mem1 ptr)
                             ('M'::('e'::('m'::('o'::('r'::('y'::(' '::('l'::('o'::('a'::('d'::(' '::('e'::('r'::('r'::('o'::('r'::[])))))))))))))))))
                             (MemoryError (ptr, pc0))) (fun v ->
                           let regs' = Intermediate.Register.set r2 v regs in
                           ret (Obj.magic exec_monad) (e0, (((gps, mem1),
                             regs'), (Pointer.inc pc0))))
                    else fail0
                           ('L'::('o'::('a'::('d'::(' '::('o'::('u'::('t'::('s'::('i'::('d'::('e'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::[]))))))))))))))))))))))
                           LoadOutsideComponent
                  | _ ->
                    fail0
                      ('N'::('o'::('t'::(' '::('a'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[])))))))))))))))))))))))))))))))))))))))
                      LoadNotAddressInReg)
               | IStore (r1, r2) ->
                 (match Intermediate.Register.get r1 regs with
                  | Ptr ptr ->
                    if Component.eqb (Pointer.component ptr)
                         (Pointer.component pc0)
                    then bind0 (Obj.magic exec_monad)
                           (lift0
                             (Obj.magic Memory.store mem1 ptr
                               (Intermediate.Register.get r2 regs))
                             ('M'::('e'::('m'::('o'::('r'::('y'::(' '::('s'::('t'::('o'::('r'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::[]))))))))))))))))))
                             (StoreMemoryError (ptr, pc0))) (fun mem' ->
                           ret (Obj.magic exec_monad) (e0, (((gps, mem'),
                             regs), (Pointer.inc pc0))))
                    else fail0
                           ('S'::('t'::('o'::('r'::('e'::(' '::('o'::('u'::('t'::('s'::('i'::('d'::('e'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::[])))))))))))))))))))))))
                           StoreOutsideComponent
                  | _ ->
                    fail0
                      ('N'::('o'::('t'::(' '::('a'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[])))))))))))))))))))))))))))))))))))))))
                      StoreNotAddressInReg)
               | IAlloc (rptr, rsize) ->
                 (match Intermediate.Register.get rsize regs with
                  | Int size1 ->
                    if Z.leb size1 0
                    then fail0
                           ('N'::('e'::('g'::('a'::('t'::('i'::('v'::('e'::(' '::('b'::('l'::('o'::('c'::('k'::(' '::('s'::('i'::('z'::('e'::[])))))))))))))))))))
                           AllocNegativeBlockSize
                    else bind0 (Obj.magic exec_monad)
                           (lift0
                             (Obj.magic Memory.alloc mem1
                               (Pointer.component pc0) (Z.to_nat size1))
                             ('A'::('l'::('l'::('o'::('c'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))))
                             (MemoryError (pc0, pc0))) (fun x ->
                           let (mem', ptr) = x in
                           let regs' =
                             Intermediate.Register.set rptr (Ptr ptr) regs
                           in
                           ret (Obj.magic exec_monad) (e0, (((gps, mem'),
                             regs'), (Pointer.inc pc0))))
                  | _ ->
                    fail0
                      ('A'::('l'::('l'::('o'::('c'::(':'::(':'::('N'::('o'::('t'::(' '::('i'::('n'::('t'::[]))))))))))))))
                      NotIntInReg)
               | IBnz (r, l) ->
                 (match Intermediate.Register.get r regs with
                  | Int val1 ->
                    ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
                       (fun _ ->
                       ret (Obj.magic exec_monad) (e0, (((gps, mem1), regs),
                         (Pointer.inc pc0))))
                       (fun _ ->
                       bind0 (Obj.magic exec_monad)
                         (lift0 (Obj.magic find_label_in_procedure g pc0 l)
                           ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('B'::('n'::('z'::(' '::('l'::('a'::('b'::('e'::('l'::[])))))))))))))))))
                           MissingLabel) (fun pc' ->
                         ret (Obj.magic exec_monad) (e0, (((gps, mem1),
                           regs), pc'))))
                       (fun _ ->
                       bind0 (Obj.magic exec_monad)
                         (lift0 (Obj.magic find_label_in_procedure g pc0 l)
                           ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('B'::('n'::('z'::(' '::('l'::('a'::('b'::('e'::('l'::[])))))))))))))))))
                           MissingLabel) (fun pc' ->
                         ret (Obj.magic exec_monad) (e0, (((gps, mem1),
                           regs), pc'))))
                       val1)
                  | _ ->
                    fail0
                      ('B'::('n'::('z'::(':'::(':'::('N'::('o'::('t'::(' '::('i'::('n'::('t'::[]))))))))))))
                      NotIntInReg)
               | IJump r ->
                 (match Intermediate.Register.get r regs with
                  | Ptr pc' ->
                    if Component.eqb (Pointer.component pc')
                         (Pointer.component pc0)
                    then ret (Obj.magic exec_monad) (e0, (((gps, mem1),
                           regs), pc'))
                    else fail0
                           ('J'::('u'::('m'::('p'::(' '::('o'::('u'::('t'::('s'::('i'::('d'::('e'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::[]))))))))))))))))))))))
                           JumpOutsideComponent
                  | _ ->
                    fail0
                      ('N'::('o'::('t'::(' '::('a'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[])))))))))))))))))))))))))))))))))))))))
                      JumpNotAddressInReg)
               | IJal l ->
                 bind0 (Obj.magic exec_monad)
                   (lift0 (Obj.magic find_label_in_component g pc0 l)
                     ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('J'::('a'::('l'::(' '::('l'::('a'::('b'::('e'::('l'::[])))))))))))))))))
                     MissingJalLabel) (fun pc' ->
                   let regs' =
                     Intermediate.Register.set R_RA (Ptr (Pointer.inc pc0))
                       regs
                   in
                   ret (Obj.magic exec_monad) (e0, (((gps, mem1), regs'),
                     pc')))
               | ICall (c', p1) ->
                 if negb (Component.eqb (Pointer.component pc0) c')
                 then if imported_procedure_b g.genv_interface
                           (Pointer.component pc0) c' p1
                      then bind0 (Obj.magic exec_monad)
                             (lift0
                               (Obj.magic Intermediate.EntryPoint.get c' p1
                                 g.genv_entrypoints)
                               ('C'::('a'::('l'::('l'::(':'::(':'::('I'::('n'::('c'::('o'::('r'::('r'::('e'::('c'::('t'::(' '::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))))))
                               InvalidEnv) (fun b ->
                             match Intermediate.Register.get R_COM regs with
                             | Int rcomval ->
                               let pc' = ((c', b), 0) in
                               let tr = (ECall ((Pointer.component pc0), p1,
                                 rcomval, c')) :: []
                               in
                               let res = (tr, (((((Pointer.inc pc0) :: gps),
                                 mem1),
                                 (Intermediate.Register.invalidate regs)),
                                 pc'))
                               in
                               ret (Obj.magic exec_monad) res
                             | Ptr _ ->
                               fail0
                                 ('C'::('a'::('l'::('l'::(':'::(':'::('P'::('t'::('r'::(' '::('i'::('n'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::(' '::('R'::('_'::('C'::('O'::('M'::[])))))))))))))))))))))))))))
                                 NoInfo1
                             | Undef ->
                               fail0
                                 ('C'::('a'::('l'::('l'::(':'::(':'::('U'::('n'::('d'::('e'::('f'::(' '::('i'::('n'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::(' '::('R'::('_'::('C'::('O'::('M'::[])))))))))))))))))))))))))))))
                                 NoInfo1)
                      else fail0
                             ('C'::('a'::('l'::('l'::(':'::(':'::('p'::('r'::('o'::('c'::('e'::('d'::('u'::('r'::('e'::(' '::('n'::('o'::('t'::(' '::('i'::('m'::('p'::('o'::('r'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))
                             InvalidEnv
                 else fail0
                        ('C'::('a'::('l'::('l'::(':'::(':'::('s'::('a'::('m'::('e'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::[]))))))))))))))))))))
                        InvalidEnv
               | IReturn ->
                 (match gps with
                  | [] ->
                    fail0
                      ('E'::('m'::('p'::('t'::('y'::(' '::('S'::('t'::('a'::('c'::('k'::[])))))))))))
                      InvalidEnv
                  | pc' :: gps' ->
                    if negb
                         (Component.eqb (Pointer.component pc0)
                           (Pointer.component pc'))
                    then (match Intermediate.Register.get R_COM regs with
                          | Int rcomval ->
                            let tr = (ERet ((Pointer.component pc0), rcomval,
                              (Pointer.component pc'))) :: []
                            in
                            ret (Obj.magic exec_monad) (tr, (((gps', mem1),
                              (Intermediate.Register.invalidate regs)), pc'))
                          | Ptr _ ->
                            fail0
                              ('R'::('e'::('t'::('u'::('r'::('n'::(':'::(':'::('P'::('t'::('r'::(' '::('i'::('n'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::(' '::('R'::('_'::('C'::('O'::('M'::[])))))))))))))))))))))))))))))
                              NoInfo1
                          | Undef ->
                            fail0
                              ('R'::('e'::('t'::('u'::('r'::('n'::(':'::(':'::('U'::('n'::('d'::('e'::('f'::(' '::('i'::('n'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::(' '::('R'::('_'::('C'::('O'::('M'::[])))))))))))))))))))))))))))))))
                              NoInfo1)
                    else fail0
                           ('R'::('e'::('t'::('u'::('r'::('n'::(':'::(':'::('s'::('a'::('m'::('e'::(' '::('c'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::[]))))))))))))))))))))))
                           InvalidEnv)
               | IHalt -> Halted e0
               | _ ->
                 ret (Obj.magic exec_monad) (e0, (((gps, mem1), regs),
                   (Pointer.inc pc0))))
            | None ->
              fail0
                ('O'::('f'::('f'::('s'::('e'::('t'::(' '::('t'::('o'::('o'::(' '::('b'::('i'::('g'::[]))))))))))))))
                (OffsetTooBig pc0))
    | None ->
      fail0
        ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('b'::('l'::('o'::('c'::('k'::[])))))))))))))
        (MissingBlock pc0))

(** val execN :
    int -> global_env -> trace -> Coq_CS.state -> (trace * Coq_CS.state)
    execution_state **)

let rec execN n g tr st =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> OutOfFuel (tr, st))
    (fun n' ->
    match eval_step g st with
    | Running t1 -> let (ntr, nst) = t1 in execN n' g (app tr ntr) nst
    | OutOfFuel s -> OutOfFuel s
    | Halted _ -> Halted tr
    | Wrong (_, msg, err) -> Wrong (tr, msg, err))
    n

(** val runp :
    int -> Intermediate.program -> (trace * Coq_CS.state) execution_state **)

let runp n p =
  let g = prepare_global_env p in
  let st = Coq_CS.initial_machine_state p in execN n g [] st

(** val newline : char list **)

let newline =
  '\n'::[]

(** val show_nat : int -> char list **)

let show_nat = (fun i ->    
  let s = string_of_int i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))

(** val show_int : int -> char list **)

let show_int = (fun i ->    
  let s = string_of_int i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))

type 'a show =
  'a -> char list
  (* singleton inductive, whose constructor was Build_Show *)

(** val show0 : 'a1 show -> 'a1 -> char list **)

let show0 show1 =
  show1

(** val showNat : int show **)

let showNat =
  show_nat

(** val showInt : int show **)

let showInt =
  show_int

(** val contents : ('a1 -> char list) -> 'a1 list -> char list **)

let rec contents s = function
| [] -> []
| h :: t1 ->
  (match t1 with
   | [] -> s h
   | _ :: _ -> append (append (s h) (','::(' '::[]))) (contents s t1))

(** val showList : 'a1 show -> 'a1 list show **)

let showList h l =
  append ('['::[]) (append (contents (show0 h) l) (']'::[]))

(** val showPair : 'a1 show -> 'a2 show -> ('a1 * 'a2) show **)

let showPair h h0 = function
| (a, b) ->
  append ('('::[])
    (append (show0 h a) (append (','::[]) (append (show0 h0 b) (')'::[]))))

(** val showOpt : 'a1 show -> 'a1 option show **)

let showOpt h = function
| Some x0 -> append ('S'::('o'::('m'::('e'::(' '::[]))))) (show0 h x0)
| None -> 'N'::('o'::('n'::('e'::[])))

(** val nl : char list **)

let nl = ['\n']

module ShowFunctions =
 struct
  (** val prepend : 'a1 -> 'a1 list -> 'a1 list **)

  let rec prepend a = function
  | [] -> []
  | h :: t1 -> a :: (h :: (prepend a t1))

  (** val intersperse : 'a1 -> 'a1 list -> 'a1 list **)

  let intersperse a = function
  | [] -> []
  | h :: t1 -> h :: (prepend a t1)

  (** val string_concat : char list list -> char list **)

  let string_concat l =
    fold_left append l []
 end

type randomSeed = Random.State.t

(** val newRandomSeed : randomSeed **)

let newRandomSeed = (Random.State.make_self_init ())

(** val randomSplit : randomSeed -> randomSeed * randomSeed **)

let randomSplit = (fun x -> (x,x))

type randomSeedTree = __randomSeedTree Lazy.t
and __randomSeedTree =
| RstNode of randomSeed * randomSeedTree * randomSeedTree

(** val mkSeedTree : randomSeed -> randomSeedTree **)

let rec mkSeedTree s =
  let (s1, s2) = randomSplit s in
  lazy (RstNode (s, (mkSeedTree s1), (mkSeedTree s2)))

type splitDirection =
| Left1
| Right1

type splitPath = splitDirection list

(** val varySeedAux : splitPath -> randomSeedTree -> randomSeed **)

let rec varySeedAux p rst =
  let RstNode (s, t1, t2) = Lazy.force rst in
  (match p with
   | [] -> s
   | s0 :: p' ->
     (match s0 with
      | Left1 -> varySeedAux p' t1
      | Right1 -> varySeedAux p' t2))

(** val varySeed : splitPath -> randomSeed -> randomSeed **)

let varySeed p s =
  varySeedAux p (mkSeedTree s)

(** val randomRNat : (int * int) -> randomSeed -> int * randomSeed **)

let randomRNat = (fun (x,y) r -> if y < x then failwith "choose called with unordered arguments" else  (x + (Random.State.int r (y - x + 1)), r))

(** val randomRInt : (int * int) -> randomSeed -> int * randomSeed **)

let randomRInt = (fun (x,y) r -> if y < x then failwith "choose called with unordered arguments" else  (x + (Random.State.int r (y - x + 1)), r))

type 'a ordType =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_OrdType *)

(** val ordNat : int ordType **)

let ordNat =
  leq

(** val ordZ : int ordType **)

let ordZ =
  Z.leb

type 'a choosableFromInterval = { super : 'a ordType;
                                  randomR : (('a * 'a) -> randomSeed ->
                                            'a * randomSeed) }

(** val randomR :
    'a1 choosableFromInterval -> ('a1 * 'a1) -> randomSeed -> 'a1 * randomSeed **)

let randomR x = x.randomR

(** val chooseNat : int choosableFromInterval **)

let chooseNat =
  { super = ordNat; randomR = randomRNat }

(** val chooseZ : int choosableFromInterval **)

let chooseZ =
  { super = ordZ; randomR = randomRInt }

(** val force : 'a1 Lazy.t -> 'a1 **)

let force = Lazy.force

type 'a rose =
| MkRose of 'a * 'a rose list Lazy.t

(** val returnRose : 'a1 -> 'a1 rose **)

let returnRose x =
  MkRose (x, (lazy []))

(** val joinRose : 'a1 rose rose -> 'a1 rose **)

let rec joinRose = function
| MkRose (r0, tts) ->
  let MkRose (a, ts) = r0 in
  MkRose (a, (lazy (app (map joinRose (force tts)) (force ts))))

(** val fmapRose : ('a1 -> 'a2) -> 'a1 rose -> 'a2 rose **)

let rec fmapRose f = function
| MkRose (x, rs) -> MkRose ((f x), (lazy (map (fmapRose f) (force rs))))

module type GenLowInterface =
 sig
  type 'x coq_G

  val returnGen : 'a1 -> 'a1 coq_G

  val bindGen : 'a1 coq_G -> ('a1 -> 'a2 coq_G) -> 'a2 coq_G

  val bindGenOpt :
    'a1 option coq_G -> ('a1 -> 'a2 option coq_G) -> 'a2 option coq_G

  val run : 'a1 coq_G -> int -> randomSeed -> 'a1

  val fmap : ('a1 -> 'a2) -> 'a1 coq_G -> 'a2 coq_G

  val sized : (int -> 'a1 coq_G) -> 'a1 coq_G

  val resize : int -> 'a1 coq_G -> 'a1 coq_G

  val promote : 'a1 coq_G rose -> 'a1 rose coq_G

  val suchThatMaybe : 'a1 coq_G -> ('a1 -> bool) -> 'a1 option coq_G

  val suchThatMaybeOpt : 'a1 option coq_G -> ('a1 -> bool) -> 'a1 option coq_G

  val choose : 'a1 choosableFromInterval -> ('a1 * 'a1) -> 'a1 coq_G

  val sample : 'a1 coq_G -> 'a1 list

  val variant : splitPath -> 'a1 coq_G -> 'a1 coq_G

  val reallyUnsafePromote : ('a1 -> 'a2 coq_G) -> ('a1 -> 'a2) coq_G

  val bindGen' : 'a1 coq_G -> ('a1 -> __ -> 'a2 coq_G) -> 'a2 coq_G
 end

module GenLow =
 struct
  type 'a coq_GenType =
    int -> randomSeed -> 'a
    (* singleton inductive, whose constructor was MkGen *)

  type 'a coq_G = 'a coq_GenType

  (** val run : 'a1 coq_G -> int -> randomSeed -> 'a1 **)

  let run g =
    g

  (** val returnGen : 'a1 -> 'a1 coq_G **)

  let returnGen x _ _ =
    x

  (** val bindGen : 'a1 coq_G -> ('a1 -> 'a2 coq_G) -> 'a2 coq_G **)

  let bindGen g k n r =
    let (r1, r2) = randomSplit r in run (k (run g n r1)) n r2

  (** val bindGenOpt :
      'a1 option coq_G -> ('a1 -> 'a2 option coq_G) -> 'a2 option coq_G **)

  let bindGenOpt g f =
    bindGen g (fun ma -> match ma with
                         | Some a -> f a
                         | None -> returnGen None)

  (** val fmap : ('a1 -> 'a2) -> 'a1 coq_G -> 'a2 coq_G **)

  let fmap f g n r =
    f (run g n r)

  (** val sized : (int -> 'a1 coq_G) -> 'a1 coq_G **)

  let sized f n r =
    run (f n) n r

  (** val resize : int -> 'a1 coq_G -> 'a1 coq_G **)

  let resize n g _ =
    g n

  (** val promote : 'a1 coq_G rose -> 'a1 rose coq_G **)

  let promote m n r =
    fmapRose (fun g -> run g n r) m

  (** val suchThatMaybeAux :
      'a1 coq_G -> ('a1 -> bool) -> int -> int -> 'a1 option coq_G **)

  let rec suchThatMaybeAux g p k n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> returnGen None)
      (fun n' ->
      bindGen
        (resize (addn (muln (Pervasives.succ (Pervasives.succ 0)) k) n) g)
        (fun x ->
        if p x
        then returnGen (Some x)
        else suchThatMaybeAux g p (Pervasives.succ k) n'))
      n

  (** val suchThatMaybe : 'a1 coq_G -> ('a1 -> bool) -> 'a1 option coq_G **)

  let suchThatMaybe g p =
    sized (fun x ->
      suchThatMaybeAux g p 0 (Pervasives.max (Pervasives.succ 0) x))

  (** val suchThatMaybeOptAux :
      'a1 option coq_G -> ('a1 -> bool) -> int -> int -> 'a1 option coq_G **)

  let rec suchThatMaybeOptAux g p k n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> returnGen None)
      (fun n' ->
      bindGen
        (resize (addn (muln (Pervasives.succ (Pervasives.succ 0)) k) n) g)
        (fun mx ->
        match mx with
        | Some x ->
          if p x
          then returnGen (Some x)
          else suchThatMaybeOptAux g p (Pervasives.succ k) n'
        | None -> suchThatMaybeOptAux g p (Pervasives.succ k) n'))
      n

  (** val suchThatMaybeOpt :
      'a1 option coq_G -> ('a1 -> bool) -> 'a1 option coq_G **)

  let suchThatMaybeOpt g p =
    sized (fun x ->
      suchThatMaybeOptAux g p 0 (Pervasives.max (Pervasives.succ 0) x))

  (** val rnds : randomSeed -> int -> randomSeed list **)

  let rec rnds rnd n' =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> [])
      (fun n'' ->
      let (rnd1, rnd2) = randomSplit rnd in rnd1 :: (rnds rnd2 n''))
      n'

  (** val createRange : int -> int list -> int list **)

  let rec createRange n acc =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> rev (0 :: acc))
      (fun n' -> createRange n' (n :: acc))
      n

  (** val choose : 'a1 choosableFromInterval -> ('a1 * 'a1) -> 'a1 coq_G **)

  let choose h range _ r =
    fst (h.randomR range r)

  (** val sample : 'a1 coq_G -> 'a1 list **)

  let sample g =
    let l =
      combine
        (rnds newRandomSeed (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))
        (createRange (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) [])
    in
    map (fun p -> let (r, n) = p in g n r) l

  (** val variant : splitPath -> 'a1 coq_G -> 'a1 coq_G **)

  let variant p g n r =
    g n (varySeed p r)

  (** val reallyUnsafeDelay : ('a1 coq_G -> 'a1) coq_G **)

  let reallyUnsafeDelay r n g =
    g r n

  (** val reallyUnsafePromote : ('a1 -> 'a2 coq_G) -> ('a1 -> 'a2) coq_G **)

  let reallyUnsafePromote m =
    bindGen reallyUnsafeDelay (fun eval -> returnGen (fun r -> eval (m r)))

  type semGenSize = __

  type semGen = __

  (** val bindGen' : 'a1 coq_G -> ('a1 -> __ -> 'a2 coq_G) -> 'a2 coq_G **)

  let bindGen' g k n r =
    let (r1, r2) = randomSplit r in run (k (run g n r1) __) n r2

  (* Unsized : logical inductive *)
  (* with constructors : Build_Unsized *)
  

  (** val unsized : __ **)

  let unsized =
    __

  (* SizedMonotonic : logical inductive *)
  (* with constructors : Build_SizedMonotonic *)
  

  (** val sizeMonotonic : __ **)

  let sizeMonotonic =
    __

  (* SizedMonotonicOpt : logical inductive *)
  (* with constructors : Build_SizedMonotonicOpt *)
  

  (** val sizeMonotonicOpt : __ **)

  let sizeMonotonicOpt =
    __

  (* SizeMonotonic : logical inductive *)
  (* with constructors : Build_SizeMonotonic *)
  

  (** val monotonic : __ **)

  let monotonic =
    __

  (* SizeMonotonicOpt : logical inductive *)
  (* with constructors : Build_SizeMonotonicOpt *)
  

  (** val monotonic_opt : __ **)

  let monotonic_opt =
    __

  (* SizeAntiMonotonicNone : logical inductive *)
  (* with constructors : Build_SizeAntiMonotonicNone *)
  

  (** val monotonic_none : __ **)

  let monotonic_none =
    __

  (** val unsizedMonotonic : __ **)

  let unsizedMonotonic =
    __

  (** val unsized_alt_def : __ **)

  let unsized_alt_def =
    __

  (** val semReturn : __ **)

  let semReturn =
    __

  (** val semReturnSize : __ **)

  let semReturnSize =
    __

  (** val unsizedReturn : __ **)

  let unsizedReturn =
    __

  (** val returnGenSizeMonotonic : __ **)

  let returnGenSizeMonotonic =
    __

  (** val returnGenSizeMonotonicOpt : __ **)

  let returnGenSizeMonotonicOpt =
    __

  (** val semBindSize : __ **)

  let semBindSize =
    __

  (** val semBindSize_subset_compat : __ **)

  let semBindSize_subset_compat =
    __

  (** val semBindSizeOpt_subset_compat : __ **)

  let semBindSizeOpt_subset_compat =
    __

  (** val monad_leftid : __ **)

  let monad_leftid =
    __

  (** val monad_rightid : __ **)

  let monad_rightid =
    __

  (** val monad_assoc : __ **)

  let monad_assoc =
    __

  (** val bindUnsized : __ **)

  let bindUnsized =
    __

  (** val bindMonotonic : __ **)

  let bindMonotonic =
    __

  (** val bindMonotonicOpt : __ **)

  let bindMonotonicOpt =
    __

  (** val bindOptMonotonicOpt : __ **)

  let bindOptMonotonicOpt =
    __

  (** val bindMonotonicStrong : __ **)

  let bindMonotonicStrong =
    __

  (** val bindMonotonicOptStrong : __ **)

  let bindMonotonicOptStrong =
    __

  (** val bindOptMonotonic : __ **)

  let bindOptMonotonic =
    __

  (** val semBindUnsized1 : __ **)

  let semBindUnsized1 =
    __

  (** val semBindUnsized2 : __ **)

  let semBindUnsized2 =
    __

  (** val semBindSizeMonotonic : __ **)

  let semBindSizeMonotonic =
    __

  (** val semBindOptSizeMonotonicIncl_r : __ **)

  let semBindOptSizeMonotonicIncl_r =
    __

  (** val semBindSizeMonotonicIncl_r : __ **)

  let semBindSizeMonotonicIncl_r =
    __

  (** val semBindOptSizeMonotonicIncl_l : __ **)

  let semBindOptSizeMonotonicIncl_l =
    __

  (** val semBindSizeMonotonicIncl_l : __ **)

  let semBindSizeMonotonicIncl_l =
    __

  (** val semBindOptSizeOpt_subset_compat : __ **)

  let semBindOptSizeOpt_subset_compat =
    __

  (** val semFmapSize : __ **)

  let semFmapSize =
    __

  (** val semFmap : __ **)

  let semFmap =
    __

  (** val fmapUnsized : __ **)

  let fmapUnsized =
    __

  (** val fmapMonotonic : __ **)

  let fmapMonotonic =
    __

  (** val semChooseSize : __ **)

  let semChooseSize =
    __

  (** val chooseUnsized : __ **)

  let chooseUnsized =
    __

  (** val semChoose : __ **)

  let semChoose =
    __

  (** val semSized : __ **)

  let semSized =
    __

  (** val semSizedSize : __ **)

  let semSizedSize =
    __

  (** val semSized_opt : __ **)

  let semSized_opt =
    __

  (** val semSized_alt : __ **)

  let semSized_alt =
    __

  (** val sizedSizeMonotonic : __ **)

  let sizedSizeMonotonic =
    __

  (** val sizedSizeMonotonicOpt : __ **)

  let sizedSizeMonotonicOpt =
    __

  (** val semResize : __ **)

  let semResize =
    __

  (** val semSizeResize : __ **)

  let semSizeResize =
    __

  (** val unsizedResize : __ **)

  let unsizedResize =
    __

  (** val semSuchThatMaybe_sound' : __ **)

  let semSuchThatMaybe_sound' =
    __

  (** val semSuchThatMaybe_complete : __ **)

  let semSuchThatMaybe_complete =
    __

  (** val promoteVariant : __ **)

  let promoteVariant =
    __

  (** val semPromote : __ **)

  let semPromote =
    __

  (** val semPromoteSize : __ **)

  let semPromoteSize =
    __

  (** val runFmap : __ **)

  let runFmap =
    __

  (** val runPromote : __ **)

  let runPromote =
    __

  (** val semFmapBind : __ **)

  let semFmapBind =
    __

  (** val suchThatMaybeMonotonicOpt : __ **)

  let suchThatMaybeMonotonicOpt =
    __

  (** val semSuchThatMaybe_sound : __ **)

  let semSuchThatMaybe_sound =
    __

  (** val suchThatMaybe_subset_compat : __ **)

  let suchThatMaybe_subset_compat =
    __

  (** val semSuchThatMaybeOpt_sound : __ **)

  let semSuchThatMaybeOpt_sound =
    __

  (** val suchThatMaybeOptMonotonicOpt : __ **)

  let suchThatMaybeOptMonotonicOpt =
    __

  (** val suchThatMaybeOpt_subset_compat : __ **)

  let suchThatMaybeOpt_subset_compat =
    __

  (** val semSuchThatMaybeOpt_complete : __ **)

  let semSuchThatMaybeOpt_complete =
    __
 end

module type GenHighInterface =
 sig
  val liftGen : ('a1 -> 'a2) -> 'a1 GenLow.coq_G -> 'a2 GenLow.coq_G

  val liftGen2 :
    ('a1 -> 'a2 -> 'a3) -> 'a1 GenLow.coq_G -> 'a2 GenLow.coq_G -> 'a3
    GenLow.coq_G

  val liftGen3 :
    ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 GenLow.coq_G -> 'a2 GenLow.coq_G -> 'a3
    GenLow.coq_G -> 'a4 GenLow.coq_G

  val liftGen4 :
    ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5) -> 'a1 GenLow.coq_G -> 'a2 GenLow.coq_G
    -> 'a3 GenLow.coq_G -> 'a4 GenLow.coq_G -> 'a5 GenLow.coq_G

  val liftGen5 :
    ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 -> 'a6) -> 'a1 GenLow.coq_G -> 'a2
    GenLow.coq_G -> 'a3 GenLow.coq_G -> 'a4 GenLow.coq_G -> 'a5 GenLow.coq_G
    -> 'a6 GenLow.coq_G

  val sequenceGen : 'a1 GenLow.coq_G list -> 'a1 list GenLow.coq_G

  val foldGen :
    ('a1 -> 'a2 -> 'a1 GenLow.coq_G) -> 'a2 list -> 'a1 -> 'a1 GenLow.coq_G

  val oneof : 'a1 GenLow.coq_G -> 'a1 GenLow.coq_G list -> 'a1 GenLow.coq_G

  val frequency :
    'a1 GenLow.coq_G -> (int * 'a1 GenLow.coq_G) list -> 'a1 GenLow.coq_G

  val backtrack :
    (int * 'a1 option GenLow.coq_G) list -> 'a1 option GenLow.coq_G

  val vectorOf : int -> 'a1 GenLow.coq_G -> 'a1 list GenLow.coq_G

  val listOf : 'a1 GenLow.coq_G -> 'a1 list GenLow.coq_G

  val elements : 'a1 -> 'a1 list -> 'a1 GenLow.coq_G

  val genPair :
    'a1 GenLow.coq_G -> 'a2 GenLow.coq_G -> ('a1 * 'a2) GenLow.coq_G

  val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

  val curry : (('a1 * 'a2) -> 'a3) -> 'a1 -> 'a2 -> 'a3

  module QcDefaultNotation :
   sig
   end

  module QcDoNotation :
   sig
   end
 end

module GenHigh =
 struct
  (** val liftGen : ('a1 -> 'a2) -> 'a1 GenLow.coq_G -> 'a2 GenLow.coq_G **)

  let liftGen f a =
    GenLow.bindGen a (fun x -> GenLow.returnGen (f x))

  (** val liftGen2 :
      ('a1 -> 'a2 -> 'a3) -> 'a1 GenLow.coq_G -> 'a2 GenLow.coq_G -> 'a3
      GenLow.coq_G **)

  let liftGen2 c m1 m2 =
    GenLow.bindGen m1 (fun x1 ->
      GenLow.bindGen m2 (fun x2 -> GenLow.returnGen (c x1 x2)))

  (** val liftGen3 :
      ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 GenLow.coq_G -> 'a2 GenLow.coq_G ->
      'a3 GenLow.coq_G -> 'a4 GenLow.coq_G **)

  let liftGen3 f m1 m2 m3 =
    GenLow.bindGen m1 (fun x1 ->
      GenLow.bindGen m2 (fun x2 ->
        GenLow.bindGen m3 (fun x3 -> GenLow.returnGen (f x1 x2 x3))))

  (** val liftGen4 :
      ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5) -> 'a1 GenLow.coq_G -> 'a2
      GenLow.coq_G -> 'a3 GenLow.coq_G -> 'a4 GenLow.coq_G -> 'a5 GenLow.coq_G **)

  let liftGen4 f m1 m2 m3 m4 =
    GenLow.bindGen m1 (fun x1 ->
      GenLow.bindGen m2 (fun x2 ->
        GenLow.bindGen m3 (fun x3 ->
          GenLow.bindGen m4 (fun x4 -> GenLow.returnGen (f x1 x2 x3 x4)))))

  (** val liftGen5 :
      ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 -> 'a6) -> 'a1 GenLow.coq_G -> 'a2
      GenLow.coq_G -> 'a3 GenLow.coq_G -> 'a4 GenLow.coq_G -> 'a5
      GenLow.coq_G -> 'a6 GenLow.coq_G **)

  let liftGen5 f m1 m2 m3 m4 m5 =
    GenLow.bindGen m1 (fun x1 ->
      GenLow.bindGen m2 (fun x2 ->
        GenLow.bindGen m3 (fun x3 ->
          GenLow.bindGen m4 (fun x4 ->
            GenLow.bindGen m5 (fun x5 -> GenLow.returnGen (f x1 x2 x3 x4 x5))))))

  (** val sequenceGen : 'a1 GenLow.coq_G list -> 'a1 list GenLow.coq_G **)

  let sequenceGen ms =
    foldr (fun m m' ->
      GenLow.bindGen m (fun x ->
        GenLow.bindGen m' (fun xs -> GenLow.returnGen (x :: xs))))
      (GenLow.returnGen []) ms

  (** val foldGen :
      ('a1 -> 'a2 -> 'a1 GenLow.coq_G) -> 'a2 list -> 'a1 -> 'a1 GenLow.coq_G **)

  let rec foldGen f l a =
    match l with
    | [] -> GenLow.returnGen a
    | x :: xs -> GenLow.bindGen (f a x) (foldGen f xs)

  (** val oneof :
      'a1 GenLow.coq_G -> 'a1 GenLow.coq_G list -> 'a1 GenLow.coq_G **)

  let oneof def gs =
    GenLow.bindGen
      (GenLow.choose chooseNat (0, (subn (length gs) (Pervasives.succ 0))))
      (nth0 def gs)

  (** val pick :
      'a1 GenLow.coq_G -> (int * 'a1 GenLow.coq_G) list -> int -> int * 'a1
      GenLow.coq_G **)

  let rec pick def xs n =
    match xs with
    | [] -> (0, def)
    | p :: xs0 ->
      let (k, x) = p in
      if leq (Pervasives.succ n) k then (k, x) else pick def xs0 (subn n k)

  (** val pickDrop :
      (int * 'a1 option GenLow.coq_G) list -> int -> (int * 'a1 option
      GenLow.coq_G) * (int * 'a1 option GenLow.coq_G) list **)

  let rec pickDrop xs n =
    match xs with
    | [] -> ((0, (GenLow.returnGen None)), [])
    | p :: xs0 ->
      let (k, x) = p in
      if leq (Pervasives.succ n) k
      then ((k, x), xs0)
      else let (p0, xs') = pickDrop xs0 (subn n k) in (p0, ((k, x) :: xs'))

  (** val sum_fst : (int * 'a1) list -> int **)

  let sum_fst gs =
    foldl (fun t1 p -> addn t1 (fst p)) 0 gs

  (** val frequency :
      'a1 GenLow.coq_G -> (int * 'a1 GenLow.coq_G) list -> 'a1 GenLow.coq_G **)

  let frequency def gs =
    let tot = sum_fst gs in
    GenLow.bindGen
      (GenLow.choose chooseNat (0, (subn tot (Pervasives.succ 0)))) (fun n ->
      snd (pick def gs n))

  (** val backtrackFuel :
      int -> int -> (int * 'a1 option GenLow.coq_G) list -> 'a1 option
      GenLow.coq_G **)

  let rec backtrackFuel fuel tot gs =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> GenLow.returnGen None)
      (fun fuel' ->
      GenLow.bindGen
        (GenLow.choose chooseNat (0, (subn tot (Pervasives.succ 0))))
        (fun n ->
        let (p, gs') = pickDrop gs n in
        let (k, g) = p in
        GenLow.bindGen g (fun ma ->
          match ma with
          | Some a -> GenLow.returnGen (Some a)
          | None -> backtrackFuel fuel' (subn tot k) gs')))
      fuel

  (** val backtrack :
      (int * 'a1 option GenLow.coq_G) list -> 'a1 option GenLow.coq_G **)

  let backtrack gs =
    backtrackFuel (length gs) (sum_fst gs) gs

  (** val vectorOf : int -> 'a1 GenLow.coq_G -> 'a1 list GenLow.coq_G **)

  let vectorOf k g =
    foldr (fun m m' ->
      GenLow.bindGen m (fun x ->
        GenLow.bindGen m' (fun xs -> GenLow.returnGen (x :: xs))))
      (GenLow.returnGen []) (nseq k g)

  (** val listOf : 'a1 GenLow.coq_G -> 'a1 list GenLow.coq_G **)

  let listOf g =
    GenLow.sized (fun n ->
      GenLow.bindGen (GenLow.choose chooseNat (0, n)) (fun k -> vectorOf k g))

  (** val elements : 'a1 -> 'a1 list -> 'a1 GenLow.coq_G **)

  let elements def l =
    let n = length l in
    GenLow.bindGen
      (GenLow.choose chooseNat (0, (subn n (Pervasives.succ 0)))) (fun n' ->
      GenLow.returnGen (nth n' l def))

  (** val semLiftGen : __ **)

  let semLiftGen =
    __

  (** val semLiftGenSize : __ **)

  let semLiftGenSize =
    __

  (** val liftGenUnsized : __ **)

  let liftGenUnsized =
    __

  (** val semLiftGen2Size : __ **)

  let semLiftGen2Size =
    __

  (** val semLiftGen2SizeMonotonic : __ **)

  let semLiftGen2SizeMonotonic =
    __

  (** val semLiftGen2Unsized1 : __ **)

  let semLiftGen2Unsized1 =
    __

  (** val semLiftGen2Unsized2 : __ **)

  let semLiftGen2Unsized2 =
    __

  (** val semLiftGen3Size : __ **)

  let semLiftGen3Size =
    __

  (** val liftGen2Unsized : __ **)

  let liftGen2Unsized =
    __

  (** val liftGen2Monotonic : __ **)

  let liftGen2Monotonic =
    __

  (** val semLiftGen4Size : __ **)

  let semLiftGen4Size =
    __

  (** val semLiftGen4SizeMonotonic : __ **)

  let semLiftGen4SizeMonotonic =
    __

  (** val liftGen4Monotonic : __ **)

  let liftGen4Monotonic =
    __

  (** val semLiftGen5Size : __ **)

  let semLiftGen5Size =
    __

  (** val semSequenceGenSize : __ **)

  let semSequenceGenSize =
    __

  (** val semSequenceGenSizeMonotonic : __ **)

  let semSequenceGenSizeMonotonic =
    __

  (** val semVectorOfSize : __ **)

  let semVectorOfSize =
    __

  (** val semVectorOfUnsized : __ **)

  let semVectorOfUnsized =
    __

  (** val vectorOfUnsized : __ **)

  let vectorOfUnsized =
    __

  (** val vectorOfMonotonic : __ **)

  let vectorOfMonotonic =
    __

  (** val semListOfSize : __ **)

  let semListOfSize =
    __

  (** val semListOfUnsized : __ **)

  let semListOfUnsized =
    __

  (** val listOfMonotonic : __ **)

  let listOfMonotonic =
    __

  (** val semOneofSize : __ **)

  let semOneofSize =
    __

  (** val semOneof : __ **)

  let semOneof =
    __

  (** val oneofMonotonic : __ **)

  let oneofMonotonic =
    __

  (** val semElementsSize : __ **)

  let semElementsSize =
    __

  (** val semElements : __ **)

  let semElements =
    __

  (** val elementsUnsized : __ **)

  let elementsUnsized =
    __

  (** val semFrequencySize : __ **)

  let semFrequencySize =
    __

  (** val semFrequency : __ **)

  let semFrequency =
    __

  (** val frequencySizeMonotonic : __ **)

  let frequencySizeMonotonic =
    __

  (** val frequencySizeMonotonic_alt : __ **)

  let frequencySizeMonotonic_alt =
    __

  (** val backtrackSizeMonotonic : __ **)

  let backtrackSizeMonotonic =
    __

  (** val backtrackSizeMonotonicOpt : __ **)

  let backtrackSizeMonotonicOpt =
    __

  (** val semBacktrackSize : __ **)

  let semBacktrackSize =
    __

  (** val bigcup_cons_setI_subset_compat_backtrack : __ **)

  let bigcup_cons_setI_subset_compat_backtrack =
    __

  (** val bigcup_cons_setI_subset_pres_backtrack : __ **)

  let bigcup_cons_setI_subset_pres_backtrack =
    __

  (** val semBacktrack_sound : __ **)

  let semBacktrack_sound =
    __

  (** val semBacktrack_complete : __ **)

  let semBacktrack_complete =
    __

  (** val semFoldGen_right : __ **)

  let semFoldGen_right =
    __

  (** val genPair :
      'a1 GenLow.coq_G -> 'a2 GenLow.coq_G -> ('a1 * 'a2) GenLow.coq_G **)

  let genPair ga gb =
    liftGen2 (fun x x0 -> (x, x0)) ga gb

  (** val curry : (('a1 * 'a2) -> 'a3) -> 'a1 -> 'a2 -> 'a3 **)

  let curry f a b =
    f (a, b)

  (** val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3 **)

  let uncurry f = function
  | (a, b) -> f a b

  (** val mergeBinds : __ **)

  let mergeBinds =
    __

  module QcDefaultNotation =
   struct
   end

  module QcDoNotation =
   struct
   end

  (** val semElemsSize : __ **)

  let semElemsSize =
    __

  (** val semOneOfSize : __ **)

  let semOneOfSize =
    __

  (** val semElems : __ **)

  let semElems =
    __

  (** val semOneOf : __ **)

  let semOneOf =
    __
 end

module AsciiOT =
 struct
  (** val compare : char -> char -> char compare0 **)

  let compare c d =
    let c0 = N.compare (n_of_ascii c) (n_of_ascii d) in
    (match c0 with
     | Eq -> EQ
     | Lt -> LT
     | Gt -> GT)
 end

module StringOT =
 struct
  type t = char list

  (** val eq_dec : char list -> char list -> bool **)

  let eq_dec =
    string_dec

  type coq_SOrdering =
  | SLT
  | SEQ
  | SGT

  (** val coq_SOrdering_rect : 'a1 -> 'a1 -> 'a1 -> coq_SOrdering -> 'a1 **)

  let coq_SOrdering_rect f f0 f1 = function
  | SLT -> f
  | SEQ -> f0
  | SGT -> f1

  (** val coq_SOrdering_rec : 'a1 -> 'a1 -> 'a1 -> coq_SOrdering -> 'a1 **)

  let coq_SOrdering_rec f f0 f1 = function
  | SLT -> f
  | SEQ -> f0
  | SGT -> f1

  (** val strcmp : char list -> char list -> coq_SOrdering **)

  let rec strcmp s1 s2 =
    match s1 with
    | [] -> (match s2 with
             | [] -> SEQ
             | _::_ -> SLT)
    | ch1::s1' ->
      (match s2 with
       | [] -> SGT
       | ch2::s2' ->
         (match AsciiOT.compare ch1 ch2 with
          | LT -> SLT
          | EQ -> strcmp s1' s2'
          | GT -> SGT))

  (** val compare : char list -> char list -> char list compare0 **)

  let rec compare s s2 =
    match s with
    | [] -> (match s2 with
             | [] -> EQ
             | _::_ -> LT)
    | a::s0 ->
      (match s2 with
       | [] -> GT
       | c2::s2' ->
         let c = AsciiOT.compare a c2 in
         (match c with
          | LT -> LT
          | EQ -> internal_eq_rew_r_dep a c2 (fun _ -> compare s0 s2') __
          | GT -> GT))
 end

module Map = Make(StringOT)

type state0 = { maxSuccessTests : int; maxDiscardedTests : int;
                maxShrinkNo : int; computeSize : (int -> int -> int);
                numSuccessTests : int; numDiscardedTests : int;
                labels : int Map.t; expectedFailure : bool;
                randomSeed0 : randomSeed; numSuccessShrinks : int;
                numTryShrinks : int }

(** val maxSuccessTests : state0 -> int **)

let maxSuccessTests x = x.maxSuccessTests

(** val maxDiscardedTests : state0 -> int **)

let maxDiscardedTests x = x.maxDiscardedTests

(** val computeSize : state0 -> int -> int -> int **)

let computeSize x = x.computeSize

(** val numSuccessTests : state0 -> int **)

let numSuccessTests x = x.numSuccessTests

(** val numDiscardedTests : state0 -> int **)

let numDiscardedTests x = x.numDiscardedTests

(** val labels : state0 -> int Map.t **)

let labels x = x.labels

(** val expectedFailure : state0 -> bool **)

let expectedFailure x = x.expectedFailure

(** val randomSeed0 : state0 -> randomSeed **)

let randomSeed0 x = x.randomSeed0

(** val numSuccessShrinks : state0 -> int **)

let numSuccessShrinks x = x.numSuccessShrinks

(** val updTryShrinks : state0 -> (int -> int) -> state0 **)

let updTryShrinks st f =
  let { maxSuccessTests = mst; maxDiscardedTests = mdt; maxShrinkNo = ms;
    computeSize = cs; numSuccessTests = nst; numDiscardedTests = ndt;
    labels = ls; expectedFailure = e1; randomSeed0 = r; numSuccessShrinks =
    nss; numTryShrinks = nts } = st
  in
  { maxSuccessTests = mst; maxDiscardedTests = mdt; maxShrinkNo = ms;
  computeSize = cs; numSuccessTests = nst; numDiscardedTests = ndt; labels =
  ls; expectedFailure = e1; randomSeed0 = r; numSuccessShrinks = nss;
  numTryShrinks = (f nts) }

(** val updSuccessShrinks : state0 -> (int -> int) -> state0 **)

let updSuccessShrinks st f =
  let { maxSuccessTests = mst; maxDiscardedTests = mdt; maxShrinkNo = ms;
    computeSize = cs; numSuccessTests = nst; numDiscardedTests = ndt;
    labels = ls; expectedFailure = e1; randomSeed0 = r; numSuccessShrinks =
    nss; numTryShrinks = nts } = st
  in
  { maxSuccessTests = mst; maxDiscardedTests = mdt; maxShrinkNo = ms;
  computeSize = cs; numSuccessTests = nst; numDiscardedTests = ndt; labels =
  ls; expectedFailure = e1; randomSeed0 = r; numSuccessShrinks = (f nss);
  numTryShrinks = nts }

type 'a genSized =
  int -> 'a GenLow.coq_G
  (* singleton inductive, whose constructor was Build_GenSized *)

(** val arbitrarySized : 'a1 genSized -> int -> 'a1 GenLow.coq_G **)

let arbitrarySized genSized0 =
  genSized0

type 'a gen =
  'a GenLow.coq_G
  (* singleton inductive, whose constructor was Build_Gen *)

(** val arbitrary : 'a1 gen -> 'a1 GenLow.coq_G **)

let arbitrary gen0 =
  gen0

type 'a shrink =
  'a -> 'a list
  (* singleton inductive, whose constructor was Build_Shrink *)

(** val shrink0 : 'a1 shrink -> 'a1 -> 'a1 list **)

let shrink0 shrink1 =
  shrink1

(** val genOfGenSized : 'a1 genSized -> 'a1 gen **)

let genOfGenSized h =
  GenLow.sized (arbitrarySized h)

(** val trace0 : char list -> 'a1 -> 'a1 **)

let trace0 = (fun l -> print_string (
   let s = Bytes.create (List.length l) in
   let rec copy i = function
    | [] -> s
    | c :: l -> s.[i] <- c; copy (i+1) l
   in copy 0 l); flush stdout; fun y -> y)

type callbackKind =
| Counterexample
| NotCounterexample

type smallResult =
| MkSmallResult of bool option * bool * char list * bool * char list list
   * char list option

type callback =
| PostTest of callbackKind * (state0 -> smallResult -> int)
| PostFinalFailure of callbackKind * (state0 -> smallResult -> int)

type result = { ok : bool option; expect : bool; reason : char list;
                interrupted : bool; stamp : char list list;
                callbacks : callback list; result_tag : char list option }

(** val ok : result -> bool option **)

let ok x = x.ok

(** val expect : result -> bool **)

let expect x = x.expect

(** val stamp : result -> char list list **)

let stamp x = x.stamp

(** val callbacks : result -> callback list **)

let callbacks x = x.callbacks

(** val result_tag : result -> char list option **)

let result_tag x = x.result_tag

(** val succeeded : result **)

let succeeded =
  { ok = (Some true); expect = true; reason = []; interrupted = false;
    stamp = []; callbacks = []; result_tag = None }

(** val failed : result **)

let failed =
  { ok = (Some false); expect = true; reason = []; interrupted = false;
    stamp = []; callbacks = []; result_tag = None }

(** val rejected : result **)

let rejected =
  { ok = None; expect = true; reason = []; interrupted = false; stamp = [];
    callbacks = []; result_tag = None }

(** val updReason : result -> char list -> result **)

let updReason r s' =
  let { ok = o; expect = e1; reason = _; interrupted = i; stamp = s;
    callbacks = c; result_tag = t1 } = r
  in
  { ok = o; expect = e1; reason = s'; interrupted = i; stamp = s; callbacks =
  c; result_tag = t1 }

(** val updOk : result -> bool option -> result **)

let updOk r o' =
  let { ok = _; expect = e1; reason = r0; interrupted = i; stamp = s;
    callbacks = c; result_tag = t1 } = r
  in
  { ok = o'; expect = e1; reason = r0; interrupted = i; stamp = s;
  callbacks = c; result_tag = t1 }

(** val addCallback : result -> callback -> result **)

let addCallback res c =
  let { ok = o; expect = e1; reason = r; interrupted = i; stamp = s;
    callbacks = cs; result_tag = t1 } = res
  in
  { ok = o; expect = e1; reason = r; interrupted = i; stamp = s; callbacks =
  (c :: cs); result_tag = t1 }

(** val addCallbacks : result -> callback list -> result **)

let addCallbacks res cs =
  let { ok = o; expect = e1; reason = r; interrupted = i; stamp = s;
    callbacks = cs'; result_tag = t1 } = res
  in
  { ok = o; expect = e1; reason = r; interrupted = i; stamp = s; callbacks =
  (app cs cs'); result_tag = t1 }

(** val addStamps : result -> char list list -> result **)

let addStamps res ss =
  let { ok = o; expect = e1; reason = r; interrupted = i; stamp = s;
    callbacks = cs; result_tag = t1 } = res
  in
  { ok = o; expect = e1; reason = r; interrupted = i; stamp = (app ss s);
  callbacks = cs; result_tag = t1 }

type qProp =
  result rose
  (* singleton inductive, whose constructor was MkProp *)

(** val unProp : qProp -> result rose **)

let unProp q =
  q

type checker = qProp GenLow.coq_G

type 'a checkable =
  'a -> checker
  (* singleton inductive, whose constructor was Build_Checkable *)

(** val checker0 : 'a1 checkable -> 'a1 -> checker **)

let checker0 checkable0 =
  checkable0

(** val liftBool : bool -> result **)

let liftBool = function
| true -> succeeded
| false ->
  updReason failed
    ('F'::('a'::('l'::('s'::('i'::('f'::('i'::('a'::('b'::('l'::('e'::[])))))))))))

(** val mapProp : 'a1 checkable -> (qProp -> qProp) -> 'a1 -> checker **)

let mapProp x f prop =
  GenLow.fmap f (checker0 x prop)

(** val mapRoseResult :
    'a1 checkable -> (result rose -> result rose) -> 'a1 -> checker **)

let mapRoseResult =
  mapProp

(** val mapTotalResult :
    'a1 checkable -> (result -> result) -> 'a1 -> checker **)

let mapTotalResult x f =
  mapRoseResult x (fmapRose f)

(** val testResult : result checkable **)

let testResult r =
  GenLow.returnGen (returnRose r)

(** val testBool : bool checkable **)

let testBool b =
  checker0 testResult (liftBool b)

(** val testUnit : unit checkable **)

let testUnit _ =
  checker0 testResult rejected

(** val testChecker : checker checkable **)

let testChecker x =
  x

(** val props' :
    'a1 checkable -> int -> ('a2 -> 'a1) -> ('a2 -> 'a2 list) -> 'a2 ->
    checker rose **)

let rec props' t1 n pf shrinker x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> MkRose ((checker0 t1 (pf x)), (lazy [])))
    (fun n' -> MkRose ((checker0 t1 (pf x)), (lazy
    (map (props' t1 n' pf shrinker) (shrinker x)))))
    n

(** val props :
    'a1 checkable -> ('a2 -> 'a1) -> ('a2 -> 'a2 list) -> 'a2 -> checker rose **)

let props h pf shrinker x =
  props' h (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    pf shrinker x

(** val shrinking :
    'a1 checkable -> ('a2 -> 'a2 list) -> 'a2 -> ('a2 -> 'a1) -> checker **)

let shrinking h shrinker x0 pf =
  GenLow.fmap (fun x -> joinRose (fmapRose unProp x))
    (GenLow.promote (props h pf shrinker x0))

(** val callback0 : 'a1 checkable -> callback -> 'a1 -> checker **)

let callback0 h cb =
  mapTotalResult h (fun r -> addCallback r cb)

(** val printTestCase : 'a1 checkable -> char list -> 'a1 -> checker **)

let printTestCase h s p =
  callback0 h (PostFinalFailure (Counterexample, (fun _ _ -> trace0 s 0))) p

(** val whenFail : 'a1 checkable -> char list -> 'a1 -> checker **)

let whenFail h str =
  callback0 h (PostFinalFailure (Counterexample, (fun _ _ ->
    trace0 (append str nl) 0)))

(** val cover :
    'a1 checkable -> bool -> int -> char list -> 'a1 -> checker **)

let cover x b _ s =
  if b
  then mapTotalResult x (fun res ->
         let { ok = o; expect = e1; reason = r; interrupted = i; stamp = st;
           callbacks = c; result_tag = t1 } = res
         in
         { ok = o; expect = e1; reason = r; interrupted = i; stamp =
         (s :: st); callbacks = c; result_tag = t1 })
  else checker0 x

(** val classify : 'a1 checkable -> bool -> char list -> 'a1 -> checker **)

let classify x b s =
  cover x b 0 s

(** val label1 : 'a1 checkable -> char list -> 'a1 -> checker **)

let label1 x s =
  classify x true s

(** val collect : 'a1 show -> 'a2 checkable -> 'a1 -> 'a2 -> checker **)

let collect h x x0 =
  label1 x (show0 h x0)

(** val forAllShrink :
    'a2 checkable -> 'a1 show -> 'a1 GenLow.coq_G -> ('a1 -> 'a1 list) ->
    ('a1 -> 'a2) -> checker **)

let forAllShrink x h gen0 shrinker pf =
  GenLow.bindGen gen0 (fun x0 ->
    shrinking testChecker shrinker x0 (fun x' ->
      printTestCase x (append (show0 h x') newline) (pf x')))

(** val addCallbacks' : result -> result -> result **)

let addCallbacks' r result1 =
  addCallbacks result1 r.callbacks

(** val addStamps' : result -> result -> result **)

let addStamps' r result1 =
  addStamps result1 r.stamp

(** val conjAux : (result -> result) -> result rose list -> result rose **)

let rec conjAux f = function
| [] -> MkRose ((f succeeded), (lazy []))
| res :: rs ->
  let MkRose (r, _) = res in
  (match r.ok with
   | Some b ->
     if b
     then conjAux (fun r' -> addStamps' r (addCallbacks' r (f r'))) rs
     else res
   | None ->
     let res' = conjAux (fun r' -> addCallbacks' r (f r')) rs in
     let MkRose (r', _) = res' in
     (match r'.ok with
      | Some b -> if b then MkRose ((updOk r' None), (lazy [])) else res'
      | None -> res'))

(** val mapGen :
    ('a1 -> 'a2 GenLow.coq_G) -> 'a1 list -> 'a2 list GenLow.coq_G **)

let mapGen f l =
  GenLow.bindGen
    (GenHigh.foldGen (fun acc a ->
      GenLow.bindGen (f a) (fun b -> GenLow.returnGen (b :: acc))) l [])
    (fun l0 -> GenLow.returnGen (rev l0))

(** val conjoin : checker list -> checker **)

let rec conjoin l =
  GenLow.bindGen (mapGen (GenHigh.liftGen unProp) l) (fun rs ->
    GenLow.returnGen (conjAux (fun x -> x) rs))

(** val gte : int -> int -> bool **)

let gte = (>=)

type args = { replay : (randomSeed * int) option; maxSuccess : int;
              maxDiscard : int; maxShrinks : int; maxSize : int; chatty : 
              bool }

(** val replay : args -> (randomSeed * int) option **)

let replay x = x.replay

(** val maxSuccess : args -> int **)

let maxSuccess x = x.maxSuccess

(** val maxDiscard : args -> int **)

let maxDiscard x = x.maxDiscard

(** val maxShrinks : args -> int **)

let maxShrinks x = x.maxShrinks

(** val maxSize : args -> int **)

let maxSize x = x.maxSize

type result0 =
| Success of int * int * (char list * int) list * char list
| GaveUp of int * (char list * int) list * char list
| Failure of int * int * int * randomSeed * int * char list
   * (char list * int) list * char list
| NoExpectedFailure of int * (char list * int) list * char list

(** val defNumTests : int **)

let defNumTests = 60000

(** val defNumDiscards : int **)

let defNumDiscards = (2 * defNumTests)

(** val defNumShrinks : int **)

let defNumShrinks = 1000

(** val defSize : int **)

let defSize = 7

(** val stdArgs : args **)

let stdArgs =
  { replay = None; maxSuccess = defNumTests; maxDiscard = defNumDiscards;
    maxShrinks = defNumShrinks; maxSize = defSize; chatty = true }

(** val roundTo : int -> int -> int **)

let roundTo n m =
  mul (Nat.div n m) m

(** val computeSize' : args -> int -> int -> int **)

let computeSize' a n d =
  if (||)
       ((||) (leq (roundTo n a.maxSize) a.maxSuccess) (leq a.maxSuccess n))
       (dvdn a.maxSuccess a.maxSize)
  then minn
         (addn (modn n a.maxSize)
           (divn d (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ 0)))))))))))) a.maxSize
  else minn
         (divn (muln (modn n a.maxSize) a.maxSize)
           (addn (modn a.maxSuccess a.maxSize)
             (divn d (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ 0))))))))))))) a.maxSize

(** val at0 : (int -> int -> int) -> int -> int -> int -> int **)

let at0 f s n d =
  if (&&) ((=) n 0) ((=) d 0) then s else f n d

(** val insertBy : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec insertBy compare1 x l = match l with
| [] -> x :: []
| h :: t1 -> if compare1 x h then x :: l else h :: (insertBy compare1 x t1)

(** val insSortBy : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec insSortBy compare1 = function
| [] -> []
| h :: t1 -> insertBy compare1 h (insSortBy compare1 t1)

(** val summary : state0 -> (char list * int) list **)

let summary st =
  let res = Map.fold (fun key0 elem acc -> (key0, elem) :: acc) st.labels []
  in
  insSortBy (fun x y -> leq (snd y) (snd x)) res

(** val doneTesting : state0 -> (int -> randomSeed -> qProp) -> result0 **)

let doneTesting st _ =
  if st.expectedFailure
  then Success ((addn st.numSuccessTests (Pervasives.succ 0)),
         st.numDiscardedTests, (summary st),
         (append
           ('+'::('+'::('+'::(' '::('P'::('a'::('s'::('s'::('e'::('d'::(' '::[])))))))))))
           (append (show0 showNat st.numSuccessTests)
             (append
               (' '::('t'::('e'::('s'::('t'::('s'::(' '::('('::[]))))))))
               (append (show0 showNat st.numDiscardedTests)
                 (' '::('d'::('i'::('s'::('c'::('a'::('r'::('d'::('s'::(')'::[])))))))))))))))
  else NoExpectedFailure (st.numSuccessTests, (summary st),
         (append
           ('*'::('*'::('*'::(' '::('F'::('a'::('i'::('l'::('e'::('d'::('!'::(' '::('P'::('a'::('s'::('s'::('e'::('d'::(' '::[])))))))))))))))))))
           (append (show0 showNat st.numSuccessTests)
             (' '::('t'::('e'::('s'::('t'::('s'::(' '::('('::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('F'::('a'::('i'::('l'::('u'::('r'::('e'::(')'::[]))))))))))))))))))))))))))))

(** val giveUp : state0 -> (int -> randomSeed -> qProp) -> result0 **)

let giveUp st _ =
  GaveUp (st.numSuccessTests, (summary st),
    (append
      ('*'::('*'::('*'::(' '::('G'::('a'::('v'::('e'::(' '::('u'::('p'::('!'::(' '::('P'::('a'::('s'::('s'::('e'::('d'::(' '::('o'::('n'::('l'::('y'::(' '::[])))))))))))))))))))))))))
      (append (show0 showNat st.numSuccessTests)
        (append (' '::('t'::('e'::('s'::('t'::('s'::[]))))))
          (append newline
            (append
              ('D'::('i'::('s'::('c'::('a'::('r'::('d'::('e'::('d'::(':'::(' '::[])))))))))))
              (show0 showNat st.numDiscardedTests)))))))

(** val callbackPostFinalFailure : state0 -> result -> int **)

let callbackPostFinalFailure st res =
  let { ok = o; expect = e1; reason = r; interrupted = i; stamp = s;
    callbacks = c; result_tag = t1 } = res
  in
  fold_left (fun acc callback1 ->
    match callback1 with
    | PostTest (_, _) -> acc
    | PostFinalFailure (_, call) ->
      addn (call st (MkSmallResult (o, e1, r, i, s, t1))) acc) c 0

(** val localMin : state0 -> result rose -> int * result **)

let rec localMin st = function
| MkRose (res, ts) ->
  (match force ts with
   | [] ->
     ((addn st.numSuccessShrinks (callbackPostFinalFailure st res)), res)
   | r0 :: t1 ->
     let MkRose (res', ts') = r0 in
     (match res'.ok with
      | Some x ->
        (match res.result_tag with
         | Some t2 ->
           (match res'.result_tag with
            | Some t3 ->
              if (&&) (negb x) (is_left (string_dec t2 t3))
              then localMin
                     (updSuccessShrinks st (fun x0 ->
                       addn x0 (Pervasives.succ 0))) (MkRose (res', ts'))
              else localMin
                     (updTryShrinks st (fun x0 ->
                       addn x0 (Pervasives.succ 0))) (MkRose (res, (lazy t1)))
            | None ->
              if (&&) (negb x) false
              then localMin
                     (updSuccessShrinks st (fun x0 ->
                       addn x0 (Pervasives.succ 0))) (MkRose (res', ts'))
              else localMin
                     (updTryShrinks st (fun x0 ->
                       addn x0 (Pervasives.succ 0))) (MkRose (res, (lazy t1))))
         | None ->
           (match res'.result_tag with
            | Some _ ->
              if (&&) (negb x) false
              then localMin
                     (updSuccessShrinks st (fun x0 ->
                       addn x0 (Pervasives.succ 0))) (MkRose (res', ts'))
              else localMin
                     (updTryShrinks st (fun x0 ->
                       addn x0 (Pervasives.succ 0))) (MkRose (res, (lazy t1)))
            | None ->
              if (&&) (negb x) true
              then localMin
                     (updSuccessShrinks st (fun x0 ->
                       addn x0 (Pervasives.succ 0))) (MkRose (res', ts'))
              else localMin
                     (updTryShrinks st (fun x0 ->
                       addn x0 (Pervasives.succ 0))) (MkRose (res, (lazy t1)))))
      | None ->
        localMin (updTryShrinks st (fun x -> addn x (Pervasives.succ 0)))
          (MkRose (res, (lazy t1)))))

(** val runATest :
    state0 -> (int -> randomSeed -> qProp) -> int -> result0 **)

let rec runATest st f maxSteps =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> giveUp st f)
    (fun maxSteps' ->
    let size1 = st.computeSize st.numSuccessTests st.numDiscardedTests in
    let (rnd1, rnd2) = randomSplit st.randomSeed0 in
    let test0 = fun st0 ->
      if gte st0.numSuccessTests st0.maxSuccessTests
      then doneTesting st0 f
      else if gte st0.numDiscardedTests st0.maxDiscardedTests
           then giveUp st0 f
           else runATest st0 f maxSteps'
    in
    let { maxSuccessTests = mst; maxDiscardedTests = mdt; maxShrinkNo = ms;
      computeSize = cs; numSuccessTests = nst; numDiscardedTests = ndt;
      labels = ls; expectedFailure = _; randomSeed0 = r; numSuccessShrinks =
      nss; numTryShrinks = nts } = st
    in
    let MkRose (res, ts) = f size1 rnd1 in
    let { ok = ok0; expect = e1; reason = reas; interrupted = _; stamp = s;
      callbacks = _; result_tag = t1 } = res
    in
    (match ok0 with
     | Some x ->
       if x
       then let ls' =
              match s with
              | [] -> ls
              | _ :: _ ->
                let s_to_add =
                  ShowFunctions.string_concat
                    (ShowFunctions.intersperse (' '::(','::(' '::[]))) s)
                in
                (match Map.find s_to_add ls with
                 | Some k -> Map.add s_to_add (addn k (Pervasives.succ 0)) ls
                 | None -> Map.add s_to_add (Pervasives.succ 0) ls)
            in
            test0 { maxSuccessTests = mst; maxDiscardedTests = mdt;
              maxShrinkNo = ms; computeSize = cs; numSuccessTests =
              (addn nst (Pervasives.succ 0)); numDiscardedTests = ndt;
              labels = ls'; expectedFailure = e1; randomSeed0 = rnd2;
              numSuccessShrinks = nss; numTryShrinks = nts }
       else let tag_text =
              match t1 with
              | Some s0 ->
                append ('T'::('a'::('g'::(':'::(' '::[]))))) (append s0 nl)
              | None -> []
            in
            let pre =
              if res.expect
              then '*'::('*'::('*'::(' '::('F'::('a'::('i'::('l'::('e'::('d'::(' '::[]))))))))))
              else '+'::('+'::('+'::(' '::('F'::('a'::('i'::('l'::('e'::('d'::(' '::('('::('a'::('s'::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(')'::(' '::[]))))))))))))))))))))))))
            in
            let (numShrinks, _) = localMin st (MkRose (res, ts)) in
            let suf =
              append ('a'::('f'::('t'::('e'::('r'::(' '::[]))))))
                (append (show0 showNat (Pervasives.succ nst))
                  (append
                    (' '::('t'::('e'::('s'::('t'::('s'::(' '::('a'::('n'::('d'::(' '::[])))))))))))
                    (append (show0 showNat numShrinks)
                      (append
                        (' '::('s'::('h'::('r'::('i'::('n'::('k'::('s'::('.'::(' '::('('::[])))))))))))
                        (append (show0 showNat ndt)
                          (' '::('d'::('i'::('s'::('c'::('a'::('r'::('d'::('s'::(')'::[])))))))))))))))
            in
            if negb res.expect
            then Success ((addn nst (Pervasives.succ 0)), ndt, (summary st),
                   (append tag_text (append pre suf)))
            else Failure ((addn nst (Pervasives.succ 0)), numShrinks, ndt, r,
                   size1, (append tag_text (append pre suf)), (summary st),
                   reas)
     | None ->
       test0 { maxSuccessTests = mst; maxDiscardedTests = mdt; maxShrinkNo =
         ms; computeSize = cs; numSuccessTests = nst; numDiscardedTests =
         (Pervasives.succ ndt); labels = ls; expectedFailure = e1;
         randomSeed0 = rnd2; numSuccessShrinks = nss; numTryShrinks = nts }))
    maxSteps

(** val test : state0 -> (int -> randomSeed -> qProp) -> result0 **)

let test st f =
  if gte st.numSuccessTests st.maxSuccessTests
  then doneTesting st f
  else if gte st.numDiscardedTests st.maxDiscardedTests
       then giveUp st f
       else let maxSteps = addn st.maxSuccessTests st.maxDiscardedTests in
            runATest st f maxSteps

(** val quickCheckWith : 'a1 checkable -> args -> 'a1 -> result0 **)

let quickCheckWith x a p =
  match a.replay with
  | Some p0 ->
    let (rnd, s) = p0 in
    let computeFun = at0 (computeSize' a) s in
    test { maxSuccessTests = a.maxSuccess; maxDiscardedTests = a.maxDiscard;
      maxShrinkNo = a.maxShrinks; computeSize = computeFun; numSuccessTests =
      0; numDiscardedTests = 0; labels = Map.empty; expectedFailure = false;
      randomSeed0 = rnd; numSuccessShrinks = 0; numTryShrinks = 0 }
      (GenLow.run (checker0 x p))
  | None ->
    let computeFun = computeSize' a in
    test { maxSuccessTests = a.maxSuccess; maxDiscardedTests = a.maxDiscard;
      maxShrinkNo = a.maxShrinks; computeSize = computeFun; numSuccessTests =
      0; numDiscardedTests = 0; labels = Map.empty; expectedFailure = false;
      randomSeed0 = newRandomSeed; numSuccessShrinks = 0; numTryShrinks = 0 }
      (GenLow.run (checker0 x p))

(** val showCollectStatistics : (char list * int) list -> char list **)

let rec showCollectStatistics = function
| [] -> []
| p :: l' ->
  let (s, n) = p in
  append (show0 showNat n)
    (append (' '::(':'::(' '::[])))
      (append s (append newline (showCollectStatistics l'))))

(** val showResult : result0 show **)

let showResult r =
  append
    (match r with
     | Success (_, _, l, s) -> append (showCollectStatistics l) s
     | GaveUp (_, l, s) -> append (showCollectStatistics l) s
     | Failure (_, _, _, _, _, s, l, _) -> append (showCollectStatistics l) s
     | NoExpectedFailure (_, l, s) -> append (showCollectStatistics l) s)
    newline

(** val quickCheck : 'a1 checkable -> 'a1 -> result0 **)

let quickCheck x p =
  quickCheckWith x stdArgs p

(** val genZSized : int genSized **)

let genZSized x =
  let z = Z.of_nat x in GenLow.choose chooseZ ((Z.opp z), z)

(** val show_value : RiscMachine.value -> char list **)

let show_value =
  show_int

(** val show_N : int -> char list **)

let show_N n =
  show_nat (N.to_nat n)

(** val show_Component_id : Component.id show **)

let show_Component_id =
  show0 showNat

(** val show_sfi_id : SFIComponent.id show **)

let show_sfi_id =
  show_N

(** val show_CN : Env.coq_CN show **)

let show_CN =
  showList show_Component_id

(** val show_addr : RiscMachine.address -> char list **)

let show_addr addr =
  let (p, o) = SFI.convert_address addr in
  let (c, s) = p in
  append ('('::('c'::('='::[])))
    (append (show_N c)
      (append (','::(' '::('s'::('='::[]))))
        (append (show0 show_sfi_id s)
          (append (','::(' '::('o'::('='::[]))))
            (append (show0 show_sfi_id o) (')'::[]))))))

(** val show_addr_i : RiscMachine.address show **)

let show_addr_i =
  show_addr

(** val show_Addr_Proc : (RiscMachine.address * Procedure.id) show **)

let show_Addr_Proc =
  showPair show_addr_i show_Component_id

(** val show_E : Env.coq_E show **)

let show_E =
  showList show_Addr_Proc

(** val show_event : event show **)

let show_event = function
| ECall (c1, pid, arg, c2) ->
  append ('['::('E'::('C'::('a'::('l'::('l'::(' '::[])))))))
    (append (show0 show_Component_id c1)
      (append (' '::[])
        (append (show0 show_Component_id pid)
          (append (' '::[])
            (append (show_int arg)
              (append (' '::[])
                (append (show0 show_Component_id c2) (']'::[]))))))))
| ERet (c1, arg, c2) ->
  append ('['::('E'::('R'::('e'::('t'::(' '::[]))))))
    (append (show0 show_Component_id c1)
      (append (' '::[])
        (append (show_int arg)
          (append (' '::[]) (append (show0 show_Component_id c2) (']'::[]))))))

(** val show_op_f : RiscMachine.ISA.binop -> char list **)

let show_op_f = function
| RiscMachine.ISA.Addition -> '+'::[]
| RiscMachine.ISA.Subtraction -> '-'::[]
| RiscMachine.ISA.Multiplication -> '*'::[]
| RiscMachine.ISA.Equality -> '='::[]
| RiscMachine.ISA.Leq -> '<'::('='::[])
| RiscMachine.ISA.BitwiseOr -> '|'::[]
| RiscMachine.ISA.BitwiseAnd -> '&'::[]
| RiscMachine.ISA.ShiftLeft -> '<'::('<'::[])

(** val show_op : RiscMachine.ISA.binop show **)

let show_op =
  show_op_f

(** val show_reg : RiscMachine.Register.t show **)

let show_reg r =
  if N.eqb r RiscMachine.Register.coq_R_ONE
  then 'R'::('_'::('O'::('N'::('E'::[]))))
  else if N.eqb r RiscMachine.Register.coq_R_COM
       then 'R'::('_'::('C'::('O'::('M'::[]))))
       else if N.eqb r RiscMachine.Register.coq_R_AUX1
            then 'R'::('_'::('A'::('U'::('X'::('1'::[])))))
            else if N.eqb r RiscMachine.Register.coq_R_AND_CODE_MASK
                 then 'R'::('_'::('A'::('N'::('D'::('_'::('C'::('O'::('D'::('E'::('_'::('M'::('A'::('S'::('K'::[]))))))))))))))
                 else if N.eqb r RiscMachine.Register.coq_R_AND_DATA_MASK
                      then 'R'::('_'::('A'::('N'::('D'::('_'::('D'::('A'::('T'::('A'::('_'::('M'::('A'::('S'::('K'::[]))))))))))))))
                      else if N.eqb r RiscMachine.Register.coq_R_OR_CODE_MASK
                           then 'R'::('_'::('O'::('R'::('_'::('C'::('O'::('D'::('E'::('_'::('M'::('A'::('S'::('K'::[])))))))))))))
                           else if N.eqb r
                                     RiscMachine.Register.coq_R_OR_DATA_MASK
                                then 'R'::('_'::('O'::('R'::('_'::('D'::('A'::('T'::('A'::('_'::('M'::('A'::('S'::('K'::[])))))))))))))
                                else if N.eqb r
                                          RiscMachine.Register.coq_R_AUX2
                                     then 'R'::('_'::('A'::('U'::('X'::('2'::[])))))
                                     else if N.eqb r
                                               RiscMachine.Register.coq_R_RA
                                          then 'R'::('A'::[])
                                          else if N.eqb r
                                                    RiscMachine.Register.coq_R_SP
                                               then 'S'::('P'::[])
                                               else if N.eqb r
                                                         RiscMachine.Register.coq_R_SFI_SP
                                                    then 'S'::('F'::('I'::('_'::('S'::('P'::[])))))
                                                    else if N.eqb r
                                                              RiscMachine.Register.coq_R_T
                                                         then 'R'::('_'::('T'::[]))
                                                         else if N.eqb r
                                                                   RiscMachine.Register.coq_R_D
                                                              then 'R'::('_'::('D'::[]))
                                                              else show_N r

(** val show_instr : RiscMachine.ISA.instr show **)

let show_instr = function
| RiscMachine.ISA.INop -> 'N'::('o'::('p'::[]))
| RiscMachine.ISA.IConst (v, r) ->
  append ('C'::('o'::('n'::('s'::('t'::(' '::[]))))))
    (append (show0 showInt v) (append (' '::[]) (show0 show_reg r)))
| RiscMachine.ISA.IMov (r1, r2) ->
  append ('M'::('o'::('v'::(' '::[]))))
    (append (show0 show_reg r1) (append (' '::[]) (show0 show_reg r2)))
| RiscMachine.ISA.IBinOp (op0, r1, r2, r3) ->
  append ('B'::('i'::('n'::('O'::('P'::(' '::[]))))))
    (append (show0 show_op op0)
      (append (' '::[])
        (append (show0 show_reg r1)
          (append (' '::[])
            (append (show0 show_reg r2)
              (append (' '::[]) (show0 show_reg r3)))))))
| RiscMachine.ISA.ILoad (r1, r2) ->
  append ('L'::('o'::('a'::('d'::(' '::[])))))
    (append (show0 show_reg r1) (append (' '::[]) (show0 show_reg r2)))
| RiscMachine.ISA.IStore (r1, r2) ->
  append ('S'::('t'::('o'::('r'::('e'::(' '::[]))))))
    (append (show0 show_reg r1) (append (' '::[]) (show0 show_reg r2)))
| RiscMachine.ISA.IBnz (r, imm) ->
  append ('B'::('n'::('Z'::(' '::[]))))
    (append (show0 show_reg r) (append (' '::[]) (show0 showInt imm)))
| RiscMachine.ISA.IJump r ->
  append ('J'::('u'::('m'::('p'::(' '::[]))))) (show0 show_reg r)
| RiscMachine.ISA.IJal addr ->
  append ('J'::('a'::('l'::(' '::[])))) (show_addr addr)
| RiscMachine.ISA.IHalt -> 'H'::('a'::('l'::('t'::[])))

(** val newline0 : char list **)

let newline0 =
  '\n'::[]

(** val show_trace : trace show **)

let show_trace =
  showList show_event

(** val show_mem : RiscMachine.Memory.t -> char list **)

let show_mem mem1 =
  fold_left (fun acc pat ->
    let (a, val1) = pat in
    (match val1 with
     | RiscMachine.Data v ->
       append acc
         (append (show_addr a)
           (append (':'::[]) (append (show_value v) newline0)))
     | RiscMachine.Instruction i ->
       append acc
         (append (show_addr a)
           (append (':'::[]) (append (show0 show_instr i) newline0)))))
    (BinNatMap.elements mem1) []

(** val show_exec_error : executionError show **)

let show_exec_error = function
| RegisterNotFound (_, reg) ->
  append
    ('R'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::('N'::('o'::('t'::('F'::('o'::('u'::('n'::('d'::[]))))))))))))))))
    (show0 show_reg reg)
| NoInfo0 -> []
| UninitializedMemory (st, addr) ->
  append
    ('U'::('n'::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('d'::('M'::('e'::('m'::('o'::('r'::('y'::(' '::('P'::('C'::('='::[])))))))))))))))))))))))
    (append (show_addr (MachineState.getPC st))
      (append
        (' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::('='::[])))))))))
        (append (show_addr addr)
          (append newline0
            (append
              (' '::('m'::('e'::('m'::('o'::('r'::('y'::(':'::[]))))))))
              (append newline0
                (append (show_mem (MachineState.getMemory st))
                  (append
                    (' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::('s'::(':'::[])))))))))))
                    (append newline0
                      (show0 (showList showInt) (MachineState.getRegs st)))))))))))
| CodeMemoryException (st, addr, i) ->
  append
    ('C'::('o'::('d'::('e'::('M'::('e'::('m'::('o'::('r'::('y'::('E'::('x'::('c'::('e'::('p'::('t'::('i'::('o'::('n'::(' '::('P'::('C'::('='::[])))))))))))))))))))))))
    (append (show_addr (MachineState.getPC st))
      (append
        (' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::(' '::('i'::('n'::(' '::('d'::('a'::('t'::('a'::(' '::('m'::('e'::('m'::('o'::('r'::('y'::('='::[]))))))))))))))))))))))))
        (append (show_addr addr)
          (append
            (' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::('s'::(' '::('i'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('i'::('o'::('n'::(' '::[]))))))))))))))))))))))
            (append (show0 show_instr i)
              (append
                (' '::('m'::('e'::('m'::('o'::('r'::('y'::(':'::[]))))))))
                (append newline0
                  (append (show_mem (MachineState.getMemory st))
                    (append
                      (' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::('s'::(':'::[])))))))))))
                      (append newline0
                        (show0 (showList showInt) (MachineState.getRegs st))))))))))))
| DataMemoryException (st, addr, val1) ->
  append
    ('D'::('a'::('t'::('a'::('M'::('e'::('m'::('o'::('r'::('y'::('E'::('x'::('c'::('e'::('p'::('t'::('i'::('o'::('n'::(' '::('P'::('C'::('='::[])))))))))))))))))))))))
    (append (show_addr (MachineState.getPC st))
      (append
        (' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::(' '::('i'::('n'::(' '::('c'::('o'::('d'::('e'::(' '::('m'::('e'::('m'::('o'::('r'::('y'::('='::[]))))))))))))))))))))))))
        (append (show_addr addr)
          (append
            (' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::('s'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::[]))))))))))))))))
            (append (show_value val1)
              (append
                (' '::('m'::('e'::('m'::('o'::('r'::('y'::(':'::[]))))))))
                (append newline0
                  (append (show_mem (MachineState.getMemory st))
                    (append
                      (' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::('s'::(':'::[])))))))))))
                      (append newline0
                        (show0 (showList showInt) (MachineState.getRegs st))))))))))))
| MissingComponentId (st, cid, cn0) ->
  append
    ('M'::('i'::('s'::('s'::('i'::('n'::('g'::('C'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::('I'::('d'::(' '::('P'::('C'::('='::[]))))))))))))))))))))))
    (append (show_addr (MachineState.getPC st))
      (append (' '::('c'::('i'::('d'::('='::[])))))
        (append (show0 show_reg cid)
          (append (' '::('C'::('N'::('='::[]))))
            (append (show0 show_CN cn0)
              (append
                (' '::('m'::('e'::('m'::('o'::('r'::('y'::(':'::[]))))))))
                (append newline0
                  (append (show_mem (MachineState.getMemory st))
                    (append
                      (' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::('s'::(':'::[])))))))))))
                      (append newline0
                        (show0 (showList showInt) (MachineState.getRegs st))))))))))))
| CallEventError (st, cid, cid', cn0, e1) ->
  append
    ('C'::('a'::('l'::('l'::('E'::('v'::('e'::('n'::('t'::('E'::('r'::('r'::('o'::('r'::(' '::('P'::('C'::('='::[]))))))))))))))))))
    (append (show_addr (MachineState.getPC st))
      (append (' '::('c'::('i'::('d'::('='::[])))))
        (append (show0 show_reg cid)
          (append (' '::('c'::('i'::('d'::('\''::('='::[]))))))
            (append (show0 show_reg cid')
              (append (' '::('C'::('N'::('='::[]))))
                (append (show0 show_CN cn0)
                  (append (' '::('E'::('='::[])))
                    (append (show0 show_E e1)
                      (append
                        (' '::('m'::('e'::('m'::('o'::('r'::('y'::(':'::[]))))))))
                        (append newline0
                          (append (show_mem (MachineState.getMemory st))
                            (append
                              (' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::('s'::(':'::[])))))))))))
                              (append newline0
                                (show0 (showList showInt)
                                  (MachineState.getRegs st))))))))))))))))
| RetEventError (st, cid, cid', cn0) ->
  append
    ('R'::('e'::('t'::('E'::('v'::('e'::('n'::('t'::('E'::('r'::('r'::('o'::('r'::(' '::('P'::('C'::('='::[])))))))))))))))))
    (append (show_addr (MachineState.getPC st))
      (append (' '::('c'::('i'::('d'::('='::[])))))
        (append (show0 show_reg cid)
          (append (' '::('c'::('i'::('d'::('\''::('='::[]))))))
            (append (show0 show_reg cid')
              (append (' '::('C'::('N'::('='::[]))))
                (append (show0 show_CN cn0)
                  (append
                    (' '::('m'::('e'::('m'::('o'::('r'::('y'::(':'::[]))))))))
                    (append newline0
                      (append (show_mem (MachineState.getMemory st))
                        (append
                          (' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::('s'::(':'::[])))))))))))
                          (append newline0
                            (show0 (showList showInt)
                              (MachineState.getRegs st))))))))))))))
| IllegalJalToZeroComponent st ->
  append
    ('I'::('l'::('l'::('e'::('g'::('a'::('l'::('J'::('a'::('l'::('T'::('o'::('Z'::('e'::('r'::('o'::('C'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::(' '::('P'::('C'::('='::[])))))))))))))))))))))))))))))
    (append (show_addr (MachineState.getPC st))
      (append (' '::('m'::('e'::('m'::('o'::('r'::('y'::(':'::[]))))))))
        (append newline0
          (append (show_mem (MachineState.getMemory st))
            (append
              (' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::('s'::(':'::[])))))))))))
              (append newline0
                (show0 (showList showInt) (MachineState.getRegs st))))))))
| IllegalJumpFromZeroComponent st ->
  append
    ('I'::('l'::('l'::('e'::('g'::('a'::('l'::('J'::('u'::('m'::('p'::('F'::('r'::('o'::('m'::('Z'::('e'::('r'::('o'::('C'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::(' '::('P'::('C'::('='::[]))))))))))))))))))))))))))))))))
    (append (show_addr (MachineState.getPC st))
      (append (' '::('m'::('e'::('m'::('o'::('r'::('y'::(':'::[]))))))))
        (append newline0
          (append (show_mem (MachineState.getMemory st))
            (append
              (' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::('s'::(':'::[])))))))))))
              (append newline0
                (show0 (showList showInt) (MachineState.getRegs st))))))))

(** val newline1 : char list **)

let newline1 =
  '\n'::[]

(** val dEBUG : bool **)

let dEBUG =
  false

(** val show_pos : int show **)

let show_pos p =
  show0 show_Component_id (Coq_Pos.to_nat p)

(** val show_fset :
    Ord.Total.coq_type -> Ord.Total.sort show -> FSet.fset_of show **)

let show_fset a h s =
  show0 (showList h) ((fset_of_subType a).val0 (Obj.magic s))

(** val show_component_interface : Component.interface show **)

let show_component_interface ci =
  append ('E'::('x'::('p'::('o'::('r'::('t'::(':'::(' '::[]))))))))
    (append
      (show0 (show_fset nat_ordType (Obj.magic show_Component_id))
        ci.Component.export)
      (append newline1
        (append ('I'::('m'::('p'::('o'::('r'::('t'::(':'::[])))))))
          (append
            (show0
              (show_fset (prod_ordType nat_ordType nat_ordType)
                (Obj.magic showPair show_Component_id show_Component_id))
              ci.Component.import) newline1))))

(** val show_ainstr : ainstr show **)

let show_ainstr = function
| INop0 -> 'I'::('N'::('o'::('p'::[])))
| ILabel0 lbl ->
  append ('I'::('L'::('a'::('b'::('e'::('l'::(' '::[])))))))
    (show0 (showPair show_pos show_reg) lbl)
| IConst0 (v, r) ->
  append ('I'::('C'::('o'::('n'::('s'::('t'::(' '::[])))))))
    (append (show0 showInt v) (append (' '::[]) (show0 show_reg r)))
| IMov0 (r1, r2) ->
  append ('I'::('M'::('o'::('v'::(' '::[])))))
    (append (show0 show_reg r1) (append (' '::[]) (show0 show_reg r2)))
| IBinOp0 (op0, r1, r2, r3) ->
  append ('I'::('B'::('i'::('n'::('o'::('p'::(' '::[])))))))
    (append (show0 show_op op0)
      (append (' '::[])
        (append (show0 show_reg r1)
          (append (' '::[])
            (append (show0 show_reg r2)
              (append (' '::[]) (show0 show_reg r3)))))))
| ILoad0 (r1, r2) ->
  append ('I'::('L'::('o'::('a'::('d'::(' '::[]))))))
    (append (show0 show_reg r1) (append (' '::[]) (show0 show_reg r2)))
| IStore0 (r1, r2) ->
  append ('I'::('S'::('t'::('o'::('r'::('e'::(' '::[])))))))
    (append (show0 show_reg r1) (append (' '::[]) (show0 show_reg r2)))
| IBnz0 (r, l) ->
  append ('I'::('B'::('n'::('z'::(' '::[])))))
    (append (show0 show_reg r)
      (append (' '::[]) (show0 (showPair show_pos show_reg) l)))
| IJump0 r ->
  append ('I'::('J'::('u'::('m'::('p'::(' '::[])))))) (show0 show_reg r)
| IJal0 l ->
  append ('I'::('J'::('a'::('l'::(' '::[])))))
    (show0 (showPair show_pos show_reg) l)
| IHalt0 -> 'I'::('H'::('a'::('l'::('t'::[]))))

(** val show_linstr : (label0 list option * ainstr) show **)

let show_linstr = function
| (ol, i) ->
  append (show0 (showOpt (showList (showPair show_pos show_reg))) ol)
    (append (':'::[]) (show0 show_ainstr i))

(** val show_lcode : lcode PMap.t PMap.t -> char list **)

let show_lcode lcode0 =
  fold_left (fun acc1 pat ->
    let (cid, pmap) = pat in
    fold_left (fun acc2 pat0 ->
      let (pid, lst) = pat0 in
      fold_left (fun acc3 elt ->
        append acc3 (append (show0 show_linstr elt) newline1)) lst
        (append acc2
          (append ('p'::('i'::('d'::('='::[]))))
            (append (show0 show_pos pid) newline1)))) (PMap.elements pmap)
      (append acc1
        (append ('c'::('i'::('d'::('='::[]))))
          (append (show0 show_pos cid) newline1)))) (PMap.elements lcode0) []

(** val show_compiler_error : compilerError show **)

let show_compiler_error = function
| NoInfo -> []
| DuplicatedLabels lcode0 -> show_lcode lcode0
| ExportedProcsLabelsC (_, _) ->
  'E'::('x'::('p'::('o'::('r'::('t'::('e'::('d'::('P'::('r'::('o'::('c'::('s'::('L'::('a'::('b'::('e'::('l'::('s'::('C'::(' '::('T'::('O'::('D'::('O'::[]))))))))))))))))))))))))
| ExportedProcsLabelsP (_, _, _) ->
  'E'::('x'::('p'::('o'::('r'::('t'::('e'::('d'::('P'::('r'::('o'::('c'::('s'::('L'::('a'::('b'::('e'::('l'::('s'::('P'::(' '::('T'::('O'::('D'::('O'::[]))))))))))))))))))))))))
| PosArg p -> show0 show_pos p
| TwoPosArg (p1, p2) ->
  append ('('::[])
    (append (show0 show_pos p1)
      (append (','::[]) (append (show0 show_pos p2) (')'::[]))))

(** val show_nmap : 'a1 show -> 'a1 nMap -> char list **)

let show_nmap h m =
  fold_left (fun acc pat ->
    let (key0, elt) = pat in
    append acc
      (append (show0 show_Component_id key0)
        (append (':'::[]) (append newline1 (append (show0 h elt) newline1)))))
    (elementsm m) []

(** val show_map_ni : 'a1 show -> 'a1 nMap show **)

let show_map_ni =
  show_nmap

(** val show_program_interface : Program.interface show **)

let show_program_interface pi =
  show_nmap show_component_interface pi

(** val show_ptr : Pointer.t show **)

let show_ptr p =
  append ('('::(' '::('c'::('i'::('d'::('='::[]))))))
    (append (show0 show_Component_id (Pointer.component p))
      (append (','::('b'::('i'::('d'::('='::[])))))
        (append (show0 show_Component_id (Pointer.block p))
          (append (','::('o'::('f'::('f'::('='::[])))))
            (append (show0 showInt (Pointer.offset p)) (')'::[]))))))

(** val show_immv : imvalue show **)

let show_immv = function
| IInt n -> append ('I'::('I'::('n'::('t'::(' '::[]))))) (show0 showInt n)
| IPtr p -> append ('I'::('P'::('t'::('r'::(' '::[]))))) (show0 show_ptr p)

(** val show_register : register show **)

let show_register = function
| R_ONE -> 'R'::('_'::('O'::('N'::('E'::[]))))
| R_COM -> 'R'::('_'::('C'::('O'::('M'::[]))))
| R_AUX1 -> 'R'::('_'::('A'::('U'::('X'::('1'::[])))))
| R_AUX2 -> 'R'::('_'::('A'::('U'::('X'::('2'::[])))))
| R_RA -> 'R'::('_'::('R'::('A'::[])))
| R_SP -> 'R'::('_'::('S'::('P'::[])))

(** val show_binop : binop show **)

let show_binop = function
| Add -> '+'::[]
| Minus -> '-'::[]
| Mul -> '*'::[]
| Eq0 -> '='::[]
| Leq -> '<'::('='::[])

(** val show_instr0 : instr show **)

let show_instr0 = function
| INop -> 'I'::('N'::('o'::('p'::[])))
| ILabel lbl ->
  append ('I'::('L'::('a'::('b'::('e'::('l'::(' '::[])))))))
    (show0 show_Component_id lbl)
| IConst (v, r) ->
  append ('I'::('C'::('o'::('n'::('s'::('t'::(' '::[])))))))
    (append (show0 show_immv v) (append (' '::[]) (show0 show_register r)))
| IMov (r1, r2) ->
  append ('I'::('M'::('o'::('v'::(' '::[])))))
    (append (show0 show_register r1)
      (append (' '::[]) (show0 show_register r2)))
| IBinOp (op0, r1, r2, r3) ->
  append ('I'::('B'::('i'::('n'::('o'::('p'::(' '::[])))))))
    (append (show0 show_binop op0)
      (append (' '::[])
        (append (show0 show_register r1)
          (append (' '::[])
            (append (show0 show_register r2)
              (append (' '::[]) (show0 show_register r3)))))))
| ILoad (r1, r2) ->
  append ('I'::('L'::('o'::('a'::('d'::(' '::[]))))))
    (append (show0 show_register r1)
      (append (' '::[]) (show0 show_register r2)))
| IStore (r1, r2) ->
  append ('I'::('S'::('t'::('o'::('r'::('e'::(' '::[])))))))
    (append (show0 show_register r1)
      (append (' '::[]) (show0 show_register r2)))
| IAlloc (r1, r2) ->
  append ('I'::('A'::('l'::('l'::('o'::('c'::(' '::[])))))))
    (append (show0 show_register r1)
      (append (' '::[]) (show0 show_register r2)))
| IBnz (r, l) ->
  append ('I'::('B'::('n'::('z'::(' '::[])))))
    (append (show0 show_register r)
      (append (' '::[]) (show0 show_Component_id l)))
| IJump r ->
  append ('I'::('J'::('u'::('m'::('p'::(' '::[])))))) (show0 show_register r)
| IJal l ->
  append ('I'::('J'::('a'::('l'::(' '::[]))))) (show0 show_Component_id l)
| ICall (cid, pid) ->
  append ('I'::('C'::('a'::('l'::('l'::(' '::[]))))))
    (append (show0 show_Component_id cid)
      (append (' '::[]) (show0 show_Component_id pid)))
| IReturn -> 'I'::('R'::('e'::('t'::('u'::('r'::('n'::[]))))))
| IHalt -> 'I'::('H'::('a'::('l'::('t'::[]))))

(** val show_value0 : value show **)

let show_value0 = function
| Int i -> show0 showInt i
| Ptr p -> show0 show_ptr p
| Undef -> 'U'::('n'::('d'::('e'::('f'::[]))))

(** val show_buffers : (Block.id * (int, value list) sum) show **)

let show_buffers = function
| (bid, y) ->
  (match y with
   | Inl n ->
     append (show0 show_Component_id bid)
       (append ('['::[]) (append (show0 show_Component_id n) (']'::[])))
   | Inr lst ->
     append (show0 show_Component_id bid)
       (append (':'::[]) (show0 (showList show_value0) lst)))

(** val show_intermediate_program : Intermediate.program show **)

let show_intermediate_program ip =
  append
    ('I'::('n'::('t'::('e'::('r'::('f'::('a'::('c'::('e'::(':'::(' '::[])))))))))))
    (append newline1
      (append (show0 show_program_interface ip.Intermediate.prog_interface)
        (append
          ('B'::('u'::('f'::('f'::('e'::('r'::('s'::(':'::(' '::[])))))))))
          (append newline1
            (append
              (show_nmap (showList show_buffers) ip.Intermediate.prog_buffers)
              (append ('C'::('o'::('d'::('e'::(':'::(' '::[]))))))
                (append newline1
                  (append
                    (show0 (show_map_ni (show_map_ni (showList show_instr0)))
                      ip.Intermediate.prog_procedures)
                    (append ('M'::('a'::('i'::('n'::(':'::(' '::[]))))))
                      (append newline1
                        (show0
                          (showOpt
                            (showPair show_Component_id show_Component_id))
                          ip.Intermediate.prog_main)))))))))))

(** val show_ip_exec_state : (trace * Coq_CS.state) execution_state show **)

let show_ip_exec_state = function
| Running _ -> 'R'::('u'::('n'::('n'::('i'::('n'::('g'::(','::(','::[]))))))))
| OutOfFuel _ ->
  'O'::('u'::('t'::('O'::('f'::('F'::('u'::('e'::('l'::(','::(','::[]))))))))))
| Halted _ -> 'H'::('a'::('l'::('t'::('e'::('d'::(','::(','::[])))))))
| Wrong (_, msg, err) ->
  append ('W'::('r'::('o'::('n'::('g'::(','::[]))))))
    (match err with
     | MissingComponentId0 cid ->
       append
         ('M'::('i'::('s'::('s'::('i'::('n'::('g'::('C'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::('I'::('d'::(','::[])))))))))))))))))))
         (if dEBUG then show0 show_ptr cid else [])
     | NegativePointerOffset _ ->
       'N'::('e'::('g'::('a'::('t'::('i'::('v'::('e'::('P'::('o'::('i'::('n'::('t'::('e'::('r'::('O'::('f'::('f'::('s'::('e'::('t'::(','::[])))))))))))))))))))))
     | LoadOutsideComponent ->
       'L'::('o'::('a'::('d'::('O'::('u'::('t'::('s'::('i'::('d'::('e'::('C'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::(','::[]))))))))))))))))))))
     | LoadNotAddressInReg ->
       'L'::('o'::('a'::('d'::('N'::('o'::('t'::('A'::('d'::('d'::('r'::('e'::('s'::('s'::('I'::('n'::('R'::('e'::('g'::(','::[])))))))))))))))))))
     | StoreOutsideComponent ->
       'S'::('t'::('o'::('r'::('e'::('O'::('u'::('t'::('s'::('i'::('d'::('e'::('C'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::(','::[])))))))))))))))))))))
     | StoreNotAddressInReg ->
       'S'::('t'::('o'::('r'::('e'::('N'::('o'::('t'::('A'::('d'::('d'::('r'::('e'::('s'::('s'::('I'::('n'::('R'::('e'::('g'::(','::[]))))))))))))))))))))
     | JumpOutsideComponent ->
       'J'::('u'::('m'::('p'::('O'::('u'::('t'::('s'::('i'::('d'::('e'::('C'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::(','::[]))))))))))))))))))))
     | JumpNotAddressInReg ->
       'J'::('u'::('m'::('p'::('N'::('o'::('t'::('A'::('d'::('d'::('r'::('e'::('s'::('s'::('I'::('n'::('R'::('e'::('g'::(','::[])))))))))))))))))))
     | MissingJalLabel ->
       'M'::('i'::('s'::('s'::('i'::('n'::('g'::('J'::('a'::('l'::('L'::('a'::('b'::('e'::('l'::(','::[])))))))))))))))
     | MissingLabel ->
       'M'::('i'::('s'::('s'::('i'::('n'::('g'::('L'::('a'::('b'::('e'::('l'::(','::[]))))))))))))
     | MissingBlock a ->
       append
         ('M'::('i'::('s'::('s'::('i'::('n'::('g'::('B'::('l'::('o'::('c'::('k'::(','::[])))))))))))))
         (if dEBUG then show0 show_ptr a else [])
     | OffsetTooBig a ->
       append
         ('O'::('f'::('f'::('s'::('e'::('t'::('T'::('o'::('o'::('B'::('i'::('g'::(','::[])))))))))))))
         (if dEBUG then show0 show_ptr a else [])
     | MemoryError (ptr, pc0) ->
       append
         ('M'::('e'::('m'::('o'::('r'::('y'::('E'::('r'::('r'::('o'::('r'::(','::[]))))))))))))
         (if dEBUG
          then append (show0 show_ptr ptr)
                 (append (' '::('p'::('c'::(':'::(' '::[])))))
                   (show0 show_ptr pc0))
          else [])
     | StoreMemoryError (ptr, pc0) ->
       append
         ('S'::('t'::('o'::('r'::('e'::('M'::('e'::('m'::('o'::('r'::('y'::('E'::('r'::('r'::('o'::('r'::(','::[])))))))))))))))))
         (if dEBUG
          then append (show0 show_ptr ptr)
                 (append (' '::('p'::('c'::(':'::(' '::[])))))
                   (show0 show_ptr pc0))
          else [])
     | NotIntInReg ->
       'N'::('o'::('t'::('I'::('n'::('t'::('I'::('n'::('R'::('e'::('g'::(','::[])))))))))))
     | AllocNegativeBlockSize ->
       'A'::('l'::('l'::('o'::('c'::('N'::('e'::('g'::('a'::('t'::('i'::('v'::('e'::('B'::('l'::('o'::('c'::('k'::('S'::('i'::('z'::('e'::(','::[]))))))))))))))))))))))
     | InvalidEnv ->
       append
         ('I'::('n'::('v'::('a'::('l'::('i'::('d'::('E'::('n'::('v'::(','::[])))))))))))
         (if dEBUG then msg else [])
     | NoInfo1 ->
       append ('N'::('o'::('I'::('n'::('f'::('o'::(','::[])))))))
         (if dEBUG then msg else []))

(** val list2fset :
    Ord.Total.coq_type -> Ord.Total.sort list -> FSet.fset_of **)

let rec list2fset a = function
| [] -> fset0 a
| x :: xs -> fsetU a (fset1 a x) (list2fset a xs)

(** val dEPTH : int **)

let dEPTH =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))

type procedure = Component.id * Procedure.id

type node = (procedure * int) * procedure list

type callGraph = node list

(** val proc_eq_dec : procedure -> procedure -> bool **)

let proc_eq_dec l1 l2 =
  let (x, x0) = l1 in
  let (i, i0) = l2 in
  if let rec f n x1 =
       (fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         (fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ -> true)
           (fun _ -> false)
           x1)
         (fun n0 ->
         (fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ -> false)
           (fun n1 -> f n0 n1)
           x1)
         n
     in f x i
  then let rec f n x1 =
         (fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ ->
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ -> true)
             (fun _ -> false)
             x1)
           (fun n0 ->
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ -> false)
             (fun n1 -> f n0 n1)
             x1)
           n
       in f x0 i0
  else false

(** val callGraph_eq_dec : callGraph -> callGraph -> bool **)

let rec callGraph_eq_dec l x =
  match l with
  | [] -> (match x with
           | [] -> true
           | _ :: _ -> false)
  | y :: l0 ->
    (match x with
     | [] -> false
     | n :: l1 ->
       if let (x0, x1) = y in
          let (p, l2) = n in
          if let (x2, x3) = x0 in
             let (p0, n0) = p in
             if let (x4, x5) = x2 in
                let (i, i0) = p0 in
                if let rec f n1 x6 =
                     (fun fO fS n -> if n=0 then fO () else fS (n-1))
                       (fun _ ->
                       (fun fO fS n -> if n=0 then fO () else fS (n-1))
                         (fun _ -> true)
                         (fun _ -> false)
                         x6)
                       (fun n2 ->
                       (fun fO fS n -> if n=0 then fO () else fS (n-1))
                         (fun _ -> false)
                         (fun n3 -> f n2 n3)
                         x6)
                       n1
                   in f x4 i
                then let rec f n1 x6 =
                       (fun fO fS n -> if n=0 then fO () else fS (n-1))
                         (fun _ ->
                         (fun fO fS n -> if n=0 then fO () else fS (n-1))
                           (fun _ -> true)
                           (fun _ -> false)
                           x6)
                         (fun n2 ->
                         (fun fO fS n -> if n=0 then fO () else fS (n-1))
                           (fun _ -> false)
                           (fun n3 -> f n2 n3)
                           x6)
                         n1
                     in f x5 i0
                else false
             then let rec f n1 x4 =
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> true)
                        (fun _ -> false)
                        x4)
                      (fun n2 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> false)
                        (fun n3 -> f n2 n3)
                        x4)
                      n1
                  in f x3 n0
             else false
          then let rec f l3 x2 =
                 match l3 with
                 | [] -> (match x2 with
                          | [] -> true
                          | _ :: _ -> false)
                 | y0 :: l4 ->
                   (match x2 with
                    | [] -> false
                    | p0 :: l5 ->
                      if let (x3, x4) = y0 in
                         let (i, i0) = p0 in
                         if let rec f0 n0 x5 =
                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                (fun _ ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ -> true)
                                  (fun _ -> false)
                                  x5)
                                (fun n1 ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ -> false)
                                  (fun n2 -> f0 n1 n2)
                                  x5)
                                n0
                            in f0 x3 i
                         then let rec f0 n0 x5 =
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ ->
                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                    (fun _ -> true)
                                    (fun _ -> false)
                                    x5)
                                  (fun n1 ->
                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                    (fun _ -> false)
                                    (fun n2 -> f0 n1 n2)
                                    x5)
                                  n0
                              in f0 x4 i0
                         else false
                      then f l4 l5
                      else false)
               in f x1 l2
          else false
       then callGraph_eq_dec l0 l1
       else false)

(** val proc_eqb : procedure -> procedure -> bool **)

let proc_eqb p1 p2 =
  (&&) ((=) (fst p1) (fst p2)) ((=) (snd p1) (snd p2))

(** val nodeGetCid : node -> Component.id **)

let nodeGetCid v =
  fst (fst (fst v))

(** val nodeGetPid : node -> Procedure.id **)

let nodeGetPid v =
  snd (fst (fst v))

(** val nodeGetProcedure : node -> procedure **)

let nodeGetProcedure v =
  fst (fst v)

(** val nodeGetDepth : node -> int **)

let nodeGetDepth v =
  snd (fst v)

(** val nodeGetCallList : node -> procedure list **)

let nodeGetCallList =
  snd

(** val existsb0 : procedure -> callGraph -> bool **)

let existsb0 p cg =
  existsb (fun n -> proc_eqb n p) (map nodeGetProcedure cg)

(** val size0 : Intermediate.program -> int **)

let size0 ip =
  fold_left (fun acc pat ->
    let (_, pmap) = pat in
    fold_left (fun acc' pat0 -> let (_, lc) = pat0 in add acc' (length lc))
      (elementsm pmap) acc) (elementsm ip.Intermediate.prog_procedures) 0

(** val buildCallGraph : Intermediate.program -> callGraph **)

let buildCallGraph ip =
  let worker =
    let rec worker wklst acc sz =
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> acc)
        (fun sz' ->
        match wklst with
        | [] -> acc
        | p0 :: xs ->
          let (p, depth) = p0 in
          if existsb0 p acc
          then worker xs acc sz'
          else (match getm nat_ordType ip.Intermediate.prog_procedures
                        (fst (Obj.magic p)) with
                | Some pmap ->
                  (match getm nat_ordType pmap (snd (Obj.magic p)) with
                   | Some lc ->
                     let calledProcs =
                       map (fun i ->
                         match i with
                         | ICall (cid, pid) -> (cid, pid)
                         | _ -> ((Pervasives.succ 0), (Pervasives.succ 0)))
                         (filter (fun i ->
                           match i with
                           | ICall (_, _) -> true
                           | _ -> false) lc)
                     in
                     let wklst' =
                       app xs
                         (map (fun x -> (x, (add depth (Pervasives.succ 0))))
                           calledProcs)
                     in
                     worker wklst' (((p, depth), calledProcs) :: acc) sz'
                   | None -> acc)
                | None -> acc))
        sz
    in worker
  in
  (match ip.Intermediate.prog_main with
   | Some p -> worker ((p, 0) :: []) [] (size0 ip)
   | None -> [])

(** val shrinkNode : node -> procedure list list **)

let shrinkNode pn =
  let lp = nodeGetCallList pn in
  map (fun nn -> firstn nn lp) (rev (seq 0 (length lp)))

(** val find0 : procedure -> callGraph -> node option **)

let find0 p cg =
  find (fun v -> proc_eqb p (nodeGetProcedure v)) cg

(** val shrinkCallGraph : procedure -> callGraph -> callGraph list **)

let shrinkCallGraph main cg =
  let worker =
    let rec worker wklst acc cg0 sz =
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> acc :: [])
        (fun sz' ->
        match wklst with
        | [] -> acc :: []
        | p :: xs ->
          if existsb0 p acc
          then worker xs acc cg0 sz'
          else (match find0 p cg0 with
                | Some n ->
                  let depth = nodeGetDepth n in
                  let calls = nodeGetCallList n in
                  if Nat.ltb depth dEPTH
                  then app
                         (flat_map (fun newCallList ->
                           worker xs
                             (fold_left (fun acc' p' ->
                               if existsb0 p' acc'
                               then acc'
                               else (match find0 p' cg0 with
                                     | Some x -> app acc' (x :: [])
                                     | None -> acc')) newCallList
                               (app acc (((p, depth), newCallList) :: [])))
                             cg0 sz') (shrinkNode n))
                         (worker (app xs calls) (app acc (n :: [])) cg0 sz')
                  else worker xs (app acc (n :: [])) cg0 sz'
                | None -> acc :: []))
        sz
    in worker
  in
  (match find0 main cg with
   | Some nodeMain ->
     remove callGraph_eq_dec cg
       (worker ((nodeGetProcedure nodeMain) :: []) [] cg
         (add (Pervasives.succ 0)
           (fold_left (fun acc v -> add acc (length (nodeGetCallList v))) cg
             0)))
   | None -> [])

(** val getComponents : callGraph -> Component.id list **)

let getComponents cg =
  nodup (=) (map nodeGetCid cg)

(** val buildInterface :
    Component.id list -> callGraph -> Program.interface **)

let buildInterface components cg =
  fold_left (fun acc cid ->
    let newExport =
      nodup (=)
        (map nodeGetPid
          (filter (fun n -> Component.eqb (nodeGetCid n) cid) cg))
    in
    let newImport =
      nodup proc_eq_dec
        (fold_left (fun acc' n ->
          if Component.eqb (nodeGetCid n) cid
          then app acc' (nodeGetCallList n)
          else acc') cg [])
    in
    let newcint = { Component.export =
      (list2fset nat_ordType (Obj.magic newExport)); Component.import =
      (list2fset (prod_ordType nat_ordType nat_ordType) (Obj.magic newImport)) }
    in
    setm nat_ordType acc (Obj.magic cid) newcint) components
    (emptym nat_ordType)

(** val buildProcedures :
    Component.id list -> callGraph -> Intermediate.program -> code nMap nMap **)

let buildProcedures _ cg ip =
  let all_procs = fold_left (fun acc n -> (nodeGetProcedure n) :: acc) cg []
  in
  let all_code =
    fold_left (fun acc pat ->
      let (y, callList) = pat in
      let (p, _) = y in
      let cid = fst p in
      let pid = snd p in
      (match getm nat_ordType ip.Intermediate.prog_procedures (Obj.magic cid) with
       | Some pmap ->
         let oldmap =
           match getm nat_ordType acc (Obj.magic cid) with
           | Some x -> x
           | None -> emptym nat_ordType
         in
         (match getm nat_ordType pmap (Obj.magic pid) with
          | Some lcode0 ->
            let newcode =
              map (fun i ->
                match i with
                | ICall (c', p') ->
                  if existsb (fun p0 -> proc_eqb p0 (c', p')) all_procs
                  then if existsb (fun p0 -> proc_eqb p0 (c', p')) callList
                       then i
                       else INop
                  else INop
                | _ -> i) lcode0
            in
            setm nat_ordType acc (Obj.magic cid)
              (setm nat_ordType oldmap (Obj.magic pid) newcode)
          | None -> acc)
       | None -> acc)) cg (emptym nat_ordType)
  in
  mapm nat_ordType (fun pmaps ->
    let declared =
      fold_left (fun acc pat ->
        let (_, li) = pat in
        fold_left (fun acc' i ->
          match i with
          | ILabel l -> l :: acc'
          | _ -> acc') li acc) (elementsm pmaps) []
    in
    mapm nat_ordType (fun li ->
      map (fun i ->
        match i with
        | IBnz (_, l) ->
          if existsb (fun l' -> (=) l' l) declared then i else INop
        | IJal l -> if existsb (fun l' -> (=) l' l) declared then i else INop
        | _ -> i) li) pmaps) all_code

(** val buildBuffers :
    Component.id list -> callGraph -> Intermediate.program ->
    (Block.id * (int, value list) sum) list nMap **)

let buildBuffers components _ ip =
  fold_left (fun acc cid ->
    match getm nat_ordType ip.Intermediate.prog_buffers (Obj.magic cid) with
    | Some x -> setm nat_ordType acc (Obj.magic cid) x
    | None -> acc) components (emptym nat_ordType)

(** val buildIntermediateProgram :
    callGraph -> Intermediate.program -> Intermediate.program **)

let buildIntermediateProgram cg ip =
  let components = getComponents cg in
  { Intermediate.prog_interface = (buildInterface components cg);
  Intermediate.prog_procedures = (buildProcedures components cg ip);
  Intermediate.prog_buffers = (buildBuffers components cg ip);
  Intermediate.prog_main = ip.Intermediate.prog_main }

(** val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let list_eqb eqb1 l1 l2 =
  (&&) (fold_left (fun acc x -> (&&) (existsb (eqb1 x) l1) acc) l2 true)
    (fold_left (fun acc x -> (&&) (existsb (eqb1 x) l2) acc) l1 true)

(** val interface_contained :
    Program.interface -> Program.interface -> bool **)

let interface_contained small big =
  fold_left (fun acc pat ->
    let (cid, cint) = pat in
    if acc
    then (match getm nat_ordType big (Obj.magic cid) with
          | Some bigCint ->
            if list_eqb (Obj.magic (=))
                 ((fset_of_subType nat_ordType).val0
                   (Obj.magic Component.export cint))
                 ((fset_of_subType nat_ordType).val0
                   (Obj.magic Component.export bigCint))
            then list_eqb (Obj.magic proc_eqb)
                   ((fset_of_subType (prod_ordType nat_ordType nat_ordType)).val0
                     (Obj.magic Component.import cint))
                   ((fset_of_subType (prod_ordType nat_ordType nat_ordType)).val0
                     (Obj.magic Component.import bigCint))
            else false
          | None -> false)
    else false) (elementsm small) true

(** val shrinkIntermediateProgram : Intermediate.program shrink **)

let shrinkIntermediateProgram ip =
  match ip.Intermediate.prog_main with
  | Some main ->
    let cg = buildCallGraph ip in
    let newip = buildIntermediateProgram cg ip in
    let newCallGraphs = shrinkCallGraph main cg in
    let shrinked =
      map (fun ncg -> buildIntermediateProgram ncg ip) newCallGraphs
    in
    if interface_contained ip.Intermediate.prog_interface
         newip.Intermediate.prog_interface
    then shrinked
    else newip :: shrinked
  | None -> []

(** val label_eq_dec0 : label -> label -> bool **)

let rec label_eq_dec0 n x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun _ -> false)
      x)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun n1 -> label_eq_dec0 n0 n1)
      x)
    n

(** val procs_eqdec : (int * int) -> (int * int) -> bool **)

let procs_eqdec p1 p2 =
  let (x, x0) = p1 in
  let (p, p0) = p2 in
  if let rec f p3 x1 =
       (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
         (fun p4 ->
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun p5 -> f p4 p5)
           (fun _ -> false)
           (fun _ -> false)
           x1)
         (fun p4 ->
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun _ -> false)
           (fun p5 -> f p4 p5)
           (fun _ -> false)
           x1)
         (fun _ ->
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun _ -> false)
           (fun _ -> false)
           (fun _ -> true)
           x1)
         p3
     in f x p
  then let rec f p3 x1 =
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun p4 ->
           (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
             (fun p5 -> f p4 p5)
             (fun _ -> false)
             (fun _ -> false)
             x1)
           (fun p4 ->
           (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
             (fun _ -> false)
             (fun p5 -> f p4 p5)
             (fun _ -> false)
             x1)
           (fun _ ->
           (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
             (fun _ -> false)
             (fun _ -> false)
             (fun _ -> true)
             x1)
           p3
       in f x0 p0
  else false

(** val mAX_PROC_PER_COMP : int **)

let mAX_PROC_PER_COMP =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))

(** val mAX_NO_BUFFERS_PER_COMP : int **)

let mAX_NO_BUFFERS_PER_COMP =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))

(** val mAX_BUFFER_SIZE : int **)

let mAX_BUFFER_SIZE =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))

(** val mAX_PROC_LENGTH : int **)

let mAX_PROC_LENGTH =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))

type test_type =
| TInstrEqual
| TInstrEqualUndef
| TStore
| TJump
| TStack
| TStackAllUndefElim
| TCompilerCorrect

type instr_type =
| Nop
| Label
| Const
| Mov
| BinOp
| Load
| Store
| Alloc
| Bnz
| Jump
| Jal
| Call
| Return
| Halt

(** val get_freq_store : instr_type -> int **)

let get_freq_store = function
| Nop -> Pervasives.succ 0
| Mov -> Pervasives.succ (Pervasives.succ 0)
| BinOp ->
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))
| Store -> 0
| Bnz -> Pervasives.succ 0
| Jump -> Pervasives.succ 0
| Jal -> Pervasives.succ 0
| Return -> Pervasives.succ (Pervasives.succ 0)
| Halt -> Pervasives.succ 0
| _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))

(** val get_freq_jump : instr_type -> int **)

let get_freq_jump = function
| Nop -> Pervasives.succ 0
| Mov -> Pervasives.succ (Pervasives.succ 0)
| BinOp ->
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))
| Bnz -> Pervasives.succ 0
| Jump ->
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))
| Jal -> Pervasives.succ 0
| Return -> Pervasives.succ (Pervasives.succ 0)
| Halt -> Pervasives.succ 0
| _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))

(** val get_freq_call : instr_type -> int **)

let get_freq_call = function
| Nop -> Pervasives.succ 0
| Mov -> Pervasives.succ (Pervasives.succ 0)
| BinOp ->
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))
| Bnz -> Pervasives.succ 0
| Jump -> Pervasives.succ 0
| Jal -> Pervasives.succ 0
| Call ->
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))))))))))
| Return -> Pervasives.succ (Pervasives.succ 0)
| Halt -> Pervasives.succ 0
| _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))

(** val get_freq : test_type -> instr_type -> int **)

let get_freq t1 i =
  match t1 with
  | TInstrEqual -> Pervasives.succ 0
  | TInstrEqualUndef -> Pervasives.succ 0
  | TStore -> get_freq_store i
  | TJump -> get_freq_jump i
  | _ -> get_freq_call i

(** val jump_undef : test_type -> bool **)

let jump_undef = function
| TInstrEqualUndef -> true
| TJump -> true
| _ -> false

(** val bnz_undef : test_type -> bool **)

let bnz_undef = function
| TInstrEqualUndef -> true
| _ -> false

(** val load_undef : test_type -> bool **)

let load_undef = function
| TInstrEqualUndef -> true
| _ -> false

(** val store_undef : test_type -> bool **)

let store_undef = function
| TInstrEqualUndef -> true
| TStore -> true
| _ -> false

(** val alloc_undef : test_type -> bool **)

let alloc_undef = function
| TInstrEqualUndef -> true
| _ -> false

(** val pos_list : int -> int list **)

let pos_list l =
  map Coq_Pos.of_nat (seq (Pervasives.succ 0) l)

(** val gen_sublist : 'a1 -> 'a1 list -> 'a1 list GenLow.coq_G **)

let gen_sublist default all = match all with
| [] -> GenLow.returnGen []
| _ :: _ ->
  GenLow.bindGen
    (GenLow.choose chooseNat ((Pervasives.succ 0), (length all))) (fun n ->
    GenHigh.vectorOf n (GenHigh.elements default all))

type prog_int0 = (int list * (int * int) list) PMap.t

(** val gen_program_interface : int list -> prog_int0 GenLow.coq_G **)

let gen_program_interface cids =
  let proc_ids =
    GenLow.bindGen
      (GenLow.choose chooseNat ((Pervasives.succ 0), mAX_PROC_PER_COMP))
      (fun n -> GenLow.returnGen (pos_list n))
  in
  GenLow.bindGen (GenHigh.vectorOf (length cids) proc_ids)
    (fun exported_procs ->
    let all_procs =
      flat_map (fun pat ->
        let (cid, lp) = pat in map (fun pid -> (cid, pid)) lp)
        (combine cids exported_procs)
    in
    GenLow.bindGen
      (GenHigh.sequenceGen
        (map (fun cid ->
          GenLow.bindGen (gen_sublist (1, 1) all_procs) (fun import_procs ->
            GenLow.returnGen
              (filter (fun pat ->
                let (cid', _) = pat in negb (Coq_Pos.eqb cid cid'))
                (nodup procs_eqdec import_procs)))) cids))
      (fun imported_procs ->
      GenLow.returnGen
        (PMapExtra.of_list
          (combine cids (combine exported_procs imported_procs)))))

(** val gen_value :
    int -> (int * (int * int) list) list -> value GenLow.coq_G **)

let gen_value cid all_buffers =
  let buffers =
    filter (fun pat -> let (cid', _) = pat in Coq_Pos.eqb cid cid')
      all_buffers
  in
  GenHigh.frequency
    (GenLow.bindGen (arbitrary (genOfGenSized genZSized)) (fun i ->
      GenLow.returnGen (Int i))) (((Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))),
    (GenLow.bindGen (arbitrary (genOfGenSized genZSized)) (fun i ->
      GenLow.returnGen (Int i)))) :: (((Pervasives.succ 0),
    (match buffers with
     | [] ->
       GenLow.bindGen (arbitrary (genOfGenSized genZSized)) (fun i ->
         GenLow.returnGen (Int i))
     | p :: xs ->
       GenLow.bindGen (GenHigh.elements p xs) (fun p' ->
         let (cid', blocks') = p' in
         (match blocks' with
          | [] ->
            GenLow.bindGen (arbitrary (genOfGenSized genZSized)) (fun i ->
              GenLow.returnGen (Int i))
          | b :: xs' ->
            let (bid, s) = b in
            GenLow.bindGen (GenHigh.elements (bid, s) xs') (fun b' ->
              let (bid', s') = b' in
              GenLow.bindGen
                (GenLow.choose chooseNat (0, (sub s' (Pervasives.succ 0))))
                (fun off ->
                GenLow.returnGen (Ptr (((Coq_Pos.to_nat cid'),
                  (Coq_Pos.to_nat bid')), (Z.of_nat off))))))))) :: []))

(** val gen_sum :
    int -> int -> (int * (int * int) list) list -> (int, value list) sum
    GenLow.coq_G **)

let gen_sum cid bsize buffers =
  GenHigh.frequency (GenLow.returnGen (Inl bsize)) (((Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))),
    (GenLow.returnGen (Inl bsize))) :: (((Pervasives.succ 0),
    (GenLow.bindGen (GenHigh.vectorOf bsize (gen_value cid buffers))
      (fun vals -> GenLow.returnGen (Inr vals)))) :: []))

(** val gen_buffers :
    int list -> (int * (int, value list) sum) list PMap.t GenLow.coq_G **)

let gen_buffers cids =
  let gen_n_buffers =
    GenLow.bindGen
      (GenLow.choose chooseNat ((Pervasives.succ 0), mAX_NO_BUFFERS_PER_COMP))
      (fun n ->
      let ids = pos_list n in
      GenLow.bindGen
        (GenHigh.vectorOf n
          (GenLow.choose chooseNat ((Pervasives.succ 0), mAX_BUFFER_SIZE)))
        (fun sizes -> GenLow.returnGen (combine ids sizes)))
  in
  GenLow.bindGen (GenHigh.vectorOf (length cids) gen_n_buffers)
    (fun buffers ->
    let comp_buffers = combine cids buffers in
    GenLow.bindGen
      (GenHigh.sequenceGen
        (map (fun pat ->
          let (cid, bl_lst) = pat in
          GenLow.bindGen
            (GenHigh.sequenceGen
              (map (fun pat0 ->
                let (_, bsize) = pat0 in gen_sum cid bsize comp_buffers)
                bl_lst)) (fun bvals ->
            GenLow.returnGen (combine (map fst bl_lst) bvals))) comp_buffers))
      (fun init_buffers0 ->
      GenLow.returnGen (PMapExtra.of_list (combine cids init_buffers0))))

(** val genOp : binop gen **)

let genOp =
  GenHigh.elements Add (Add :: (Minus :: (Mul :: (Eq0 :: (Leq :: [])))))

(** val genRegs : register gen **)

let genRegs =
  GenHigh.elements R_ONE
    (R_ONE :: (R_COM :: (R_AUX1 :: (R_AUX2 :: (R_RA :: (R_SP :: []))))))

(** val genPointer :
    int -> (int * (int, value list) sum) list PMap.t -> imvalue option
    GenLow.coq_G **)

let genPointer cid buffers =
  let nat_cid = Coq_Pos.to_nat cid in
  (match PMap.find cid buffers with
   | Some lst ->
     (match lst with
      | [] -> GenLow.returnGen None
      | b :: xs ->
        GenLow.bindGen (GenHigh.elements b xs) (fun _ ->
          let (bid, bs) = b in
          let nat_bid = Coq_Pos.to_nat bid in
          (match bs with
           | Inl sz ->
             if (=) sz 0
             then GenLow.returnGen None
             else if (=) sz (Pervasives.succ 0)
                  then GenLow.returnGen (Some (IPtr ((nat_cid, nat_bid), 0)))
                  else let up = sub sz (Pervasives.succ 0) in
                       GenLow.bindGen (GenLow.choose chooseNat (0, up))
                         (fun offset0 ->
                         GenLow.returnGen (Some (IPtr ((nat_cid, nat_bid),
                           (Z.of_nat offset0)))))
           | Inr lst0 ->
             if (=) (length lst0) (Pervasives.succ 0)
             then GenLow.returnGen (Some (IPtr ((nat_cid, nat_bid), 0)))
             else GenLow.bindGen
                    (GenLow.choose chooseNat (0,
                      (sub (length lst0) (Pervasives.succ 0))))
                    (fun offset0 ->
                    GenLow.returnGen (Some (IPtr ((nat_cid, nat_bid),
                      (Z.of_nat offset0))))))))
   | None -> GenLow.returnGen None)

(** val genPtrImVal :
    prog_int0 -> (int * (int, value list) sum) list PMap.t -> int -> bool ->
    imvalue option GenLow.coq_G **)

let genPtrImVal pi buffers cid = function
| true -> genPointer cid buffers
| false ->
  GenHigh.backtrack (((Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))), (genPointer cid buffers)) :: (((Pervasives.succ
    0),
    (GenLow.bindGen (GenHigh.elements 1 (map fst (PMap.elements pi)))
      (fun id0 -> genPointer id0 buffers))) :: []))

(** val genIntImVal : imvalue GenLow.coq_G **)

let genIntImVal =
  GenLow.bindGen (arbitrary (genOfGenSized genZSized)) (fun n ->
    GenLow.returnGen (IInt n))

(** val genImVal :
    prog_int0 -> (int * (int, value list) sum) list PMap.t -> int -> imvalue
    GenLow.coq_G **)

let genImVal pi buffers cid =
  let genImValAux =
    GenLow.bindGen (genPtrImVal pi buffers cid false) (fun res ->
      match res with
      | Some ptr -> GenLow.returnGen ptr
      | None -> genIntImVal)
  in
  GenHigh.frequency genIntImVal (((Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))),
    genIntImVal) :: (((Pervasives.succ 0), genImValAux) :: []))

(** val genIConst :
    prog_int0 -> (int * (int, value list) sum) list PMap.t -> int -> instr
    list GenLow.coq_G **)

let genIConst pi buffers cid =
  GenLow.bindGen (genImVal pi buffers cid) (fun v ->
    GenLow.bindGen (arbitrary genRegs) (fun r ->
      GenLow.returnGen ((IConst (v, r)) :: [])))

(** val gen2Reg :
    (register -> register -> instr) -> instr list GenLow.coq_G **)

let gen2Reg it =
  GenLow.bindGen (arbitrary genRegs) (fun r1 ->
    GenLow.bindGen (arbitrary genRegs) (fun r2 ->
      GenLow.returnGen ((it r1 r2) :: [])))

(** val genMemReg :
    (register -> register -> instr) -> prog_int0 -> (int * (int, value list)
    sum) list PMap.t -> int -> instr list GenLow.coq_G **)

let genMemReg it pi buffers cid =
  GenLow.bindGen (arbitrary genRegs) (fun r1 ->
    GenLow.bindGen (arbitrary genRegs) (fun r2 ->
      GenLow.bindGen (genPtrImVal pi buffers cid true) (fun res ->
        match res with
        | Some ptr ->
          GenLow.returnGen ((IConst (ptr, r1)) :: ((it r1 r2) :: []))
        | None -> GenLow.returnGen ((it r1 r2) :: []))))

(** val genIAlloc : test_type -> instr list GenLow.coq_G **)

let genIAlloc t1 =
  GenLow.bindGen (arbitrary genRegs) (fun r1 ->
    GenLow.bindGen (arbitrary genRegs) (fun r2 ->
      if alloc_undef t1
      then GenLow.returnGen ((IAlloc (r1, r2)) :: [])
      else GenLow.bindGen
             (GenLow.choose chooseNat (0,
               (sub (N.to_nat SFI.coq_SLOT_SIZE) (Pervasives.succ 0))))
             (fun v ->
             GenLow.returnGen ((IConst ((IInt (Z.of_nat v)), r2)) :: ((IAlloc
               (r1, r2)) :: [])))))

(** val genILoad :
    test_type -> prog_int0 -> (int * (int, value list) sum) list PMap.t ->
    int -> instr list GenLow.coq_G **)

let genILoad t1 pi buffers cid =
  if load_undef t1
  then gen2Reg (fun x x0 -> ILoad (x, x0))
  else genMemReg (fun x x0 -> ILoad (x, x0)) pi buffers cid

(** val genIStore :
    test_type -> prog_int0 -> (int * (int, value list) sum) list PMap.t ->
    int -> instr list GenLow.coq_G **)

let genIStore t1 pi buffers cid =
  if store_undef t1
  then gen2Reg (fun x x0 -> IStore (x, x0))
  else genMemReg (fun x x0 -> IStore (x, x0)) pi buffers cid

(** val genIBinOp : instr list GenLow.coq_G **)

let genIBinOp =
  GenLow.bindGen (arbitrary genOp) (fun op0 ->
    GenLow.bindGen (arbitrary genRegs) (fun r1 ->
      GenLow.bindGen (arbitrary genRegs) (fun r2 ->
        GenLow.bindGen (arbitrary genRegs) (fun r3 ->
          GenLow.returnGen ((IBinOp (op0, r1, r2, r3)) :: [])))))

(** val genIJump : test_type -> instr list GenLow.coq_G **)

let genIJump t1 =
  if jump_undef t1
  then GenLow.bindGen (arbitrary genRegs) (fun r ->
         GenLow.returnGen ((IJump r) :: []))
  else GenLow.bindGen (arbitrary genRegs) (fun r ->
         GenLow.bindGen
           (GenLow.choose chooseNat ((Pervasives.succ 0),
             (sub (N.to_nat SFI.coq_COMP_MAX) (Pervasives.succ 0))))
           (fun cid ->
           GenLow.bindGen
             (GenLow.choose chooseNat ((Pervasives.succ 0),
               mAX_PROC_PER_COMP)) (fun pid ->
             GenLow.bindGen
               (GenLow.choose chooseNat ((Pervasives.succ 0),
                 (add (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ 0)))))))))))))))) mAX_PROC_LENGTH)))
               (fun offset0 ->
               let v =
                 SFI.address_of (N.of_nat cid)
                   (N.mul ((fun p->2*p) 1) (N.of_nat pid)) (N.of_nat offset0)
               in
               GenLow.returnGen ((IConst ((IInt (Z.of_nat (N.to_nat v))),
                 r)) :: ((IJump R_RA) :: []))))))

(** val genICall : prog_int0 -> int -> int -> instr list GenLow.coq_G **)

let genICall pi cid _ =
  match PMap.find cid pi with
  | Some comp_interface ->
    let imports = snd comp_interface in
    (match imports with
     | [] -> GenLow.returnGen (INop :: [])
     | p :: _ ->
       GenLow.bindGen (GenHigh.elements p imports) (fun p0 ->
         GenLow.bindGen (arbitrary (genOfGenSized genZSized)) (fun v ->
           let (cid', pid') = p0 in
           let call_instr = ICall ((Coq_Pos.to_nat cid'),
             (Coq_Pos.to_nat pid'))
           in
           let const_instr = IConst ((IInt v), R_COM) in
           GenLow.returnGen (const_instr :: (call_instr :: [])))))
  | None -> GenLow.returnGen (INop :: [])

(** val genIJal : instr list GenLow.coq_G **)

let genIJal =
  GenLow.bindGen
    (GenLow.choose chooseNat ((Pervasives.succ 0), (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))) (fun l -> GenLow.returnGen ((IJal l) :: []))

(** val genIBnz : test_type -> int -> int -> instr list GenLow.coq_G **)

let genIBnz t1 first_label lbl =
  if bnz_undef t1
  then GenLow.bindGen (arbitrary genRegs) (fun r ->
         if Nat.ltb first_label
              (add lbl (Pervasives.succ (Pervasives.succ (Pervasives.succ
                0))))
         then GenLow.bindGen
                (GenLow.choose chooseNat (first_label,
                  (add lbl (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    0)))))) (fun target ->
                GenLow.returnGen ((IBnz (r, target)) :: []))
         else GenLow.bindGen
                (GenLow.choose chooseNat (lbl,
                  (add lbl (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    0)))))) (fun target ->
                GenLow.returnGen ((IBnz (r, target)) :: [])))
  else GenLow.bindGen (arbitrary genRegs) (fun r ->
         GenLow.bindGen (arbitrary (genOfGenSized genZSized)) (fun v ->
           if Nat.ltb first_label
                (add lbl (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  0))))
           then GenLow.bindGen
                  (GenLow.choose chooseNat (first_label,
                    (add lbl (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ 0)))))) (fun target ->
                  GenLow.returnGen ((IConst ((IInt v), r)) :: ((IBnz (r,
                    target)) :: [])))
           else GenLow.bindGen
                  (GenLow.choose chooseNat (lbl,
                    (add lbl (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ 0)))))) (fun target ->
                  GenLow.returnGen ((IConst ((IInt v), r)) :: ((IBnz (r,
                    target)) :: [])))))

(** val genILabel : int -> instr list GenLow.coq_G **)

let genILabel lbl =
  GenLow.returnGen ((ILabel lbl) :: [])

(** val delared_labels_in_proc : code -> int list **)

let delared_labels_in_proc proc =
  map (fun i -> match i with
                | ILabel l -> l
                | _ -> Pervasives.succ 0)
    (filter (fun i -> match i with
                      | ILabel _ -> true
                      | _ -> false) proc)

(** val get_missing_labels : code -> label list **)

let get_missing_labels proc =
  let decl = delared_labels_in_proc proc in
  let uses =
    map (fun i -> match i with
                  | IBnz (_, l) -> l
                  | _ -> Pervasives.succ 0)
      (filter (fun i -> match i with
                        | IBnz (_, _) -> true
                        | _ -> false) proc)
  in
  nodup label_eq_dec0
    (filter (fun l -> (=) 0 (count_occ label_eq_dec0 decl l)) uses)

(** val gen_proc_with_labels :
    instr list -> label list -> instr list GenLow.coq_G **)

let rec gen_proc_with_labels proc missing_labels = match missing_labels with
| [] -> GenLow.returnGen proc
| lbl :: xs ->
  GenLow.bindGen
    (GenLow.choose chooseNat (0,
      (sub (length missing_labels) (Pervasives.succ 0)))) (fun pos ->
    let new_proc =
      app (firstn pos proc) (app ((ILabel lbl) :: []) (skipn pos proc))
    in
    gen_proc_with_labels new_proc xs)

(** val gen_instr :
    int -> int -> test_type -> prog_int0 -> (int * (int, value list) sum)
    list PMap.t -> int -> int -> instr list GenLow.coq_G **)

let gen_instr first_label next_label0 t1 pi buffers cid pid =
  GenHigh.frequency (GenLow.returnGen (INop :: [])) (((get_freq t1 Nop),
    (GenLow.returnGen (INop :: []))) :: (((get_freq t1 Const),
    (genIConst pi buffers cid)) :: (((get_freq t1 Label),
    (genILabel next_label0)) :: (((get_freq t1 Mov),
    (gen2Reg (fun x x0 -> IMov (x, x0)))) :: (((get_freq t1 BinOp),
    genIBinOp) :: (((get_freq t1 Load),
    (genILoad t1 pi buffers cid)) :: (((get_freq t1 Store),
    (genIStore t1 pi buffers cid)) :: (((get_freq t1 Bnz),
    (genIBnz t1 first_label next_label0)) :: (((get_freq t1 Jump),
    (genIJump t1)) :: (((get_freq t1 Jal), genIJal) :: (((get_freq t1 Call),
    (genICall pi cid pid)) :: (((get_freq t1 Alloc),
    (genIAlloc t1)) :: (((get_freq t1 Halt),
    (GenLow.returnGen (IHalt :: []))) :: (((get_freq t1 Return),
    (GenLow.returnGen (IReturn :: []))) :: []))))))))))))))

(** val gen_procedure :
    test_type -> prog_int0 -> (int * (int, value list) sum) list PMap.t ->
    int -> int -> int -> code GenLow.coq_G **)

let gen_procedure t1 pi buffers cid pid next_label0 =
  let rec gen_proc_rec proc len first_lbl lbl =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      GenLow.bindGen (gen_proc_with_labels proc (get_missing_labels proc))
        (fun p -> GenLow.returnGen (app p (IReturn :: []))))
      (fun len' ->
      GenLow.bindGen (gen_instr first_lbl lbl t1 pi buffers cid pid)
        (fun il ->
        match il with
        | [] -> gen_proc_rec (app proc il) len' first_lbl lbl
        | i :: l ->
          (match i with
           | ILabel _ ->
             (match l with
              | [] ->
                gen_proc_rec (app proc il) len' first_lbl
                  (add lbl (Pervasives.succ 0))
              | _ :: _ -> gen_proc_rec (app proc il) len' first_lbl lbl)
           | IReturn ->
             (match l with
              | [] ->
                GenLow.bindGen
                  (gen_proc_with_labels proc (get_missing_labels proc))
                  (fun p -> GenLow.returnGen (app p il))
              | _ :: _ -> gen_proc_rec (app proc il) len' first_lbl lbl)
           | IHalt ->
             (match l with
              | [] ->
                GenLow.bindGen
                  (gen_proc_with_labels proc (get_missing_labels proc))
                  (fun p -> GenLow.returnGen (app p il))
              | _ :: _ -> gen_proc_rec (app proc il) len' first_lbl lbl)
           | _ -> gen_proc_rec (app proc il) len' first_lbl lbl)))
      len
  in gen_proc_rec [] mAX_PROC_LENGTH next_label0 next_label0

(** val max_label : code PMap.t -> int **)

let max_label procs =
  fold_left (fun acc pat ->
    let (_, proc) = pat in
    fold_left (fun acc' i ->
      match i with
      | ILabel l -> if Nat.ltb acc' l then l else acc'
      | _ -> acc') proc acc) (PMap.elements procs) (Pervasives.succ 0)

(** val gen_procedures :
    test_type -> prog_int0 -> (int * (int, value list) sum) list PMap.t ->
    code PMap.t PMap.t GenLow.coq_G **)

let gen_procedures t1 pi buffers =
  GenHigh.foldGen (fun acc pat ->
    let (cid, comp_interface) = pat in
    GenLow.bindGen
      (let (lexp, _) = comp_interface in
       GenHigh.foldGen (fun acc0 pid ->
         GenLow.bindGen
           (gen_procedure t1 pi buffers cid pid
             (add (max_label acc0) (Pervasives.succ 0))) (fun proc ->
           GenLow.returnGen (PMap.add pid proc acc0))) lexp PMap.empty)
      (fun proc_map ->
      let all_decl_labels =
        fold_left app
          (map (fun p -> delared_labels_in_proc (snd p))
            (PMap.elements proc_map)) []
      in
      let uses =
        fold_left app
          (map (fun p ->
            map (fun i -> match i with
                          | IJal l -> l
                          | _ -> Pervasives.succ 0)
              (filter (fun i -> match i with
                                | IJal _ -> true
                                | _ -> false) (snd p)))
            (PMap.elements proc_map)) []
      in
      let lbls =
        nodup label_eq_dec0
          (filter (fun l ->
            (=) 0 (count_occ label_eq_dec0 all_decl_labels l)) uses)
      in
      (match PMap.elements proc_map with
       | [] -> GenLow.returnGen (PMap.add cid proc_map acc)
       | p :: _ ->
         let (pid, code1) = p in
         GenLow.returnGen
           (PMap.add cid
             (PMap.add pid (app (map (fun l -> ILabel l) lbls) code1)
               proc_map) acc)))) (PMap.elements pi) PMap.empty

(** val gen_main : prog_int0 -> (int * int) GenLow.coq_G **)

let gen_main pi =
  GenLow.bindGen (GenHigh.elements 1 (map fst (PMap.elements pi)))
    (fun cid ->
    match PMap.find cid pi with
    | Some cint ->
      GenLow.bindGen (GenHigh.elements 1 (fst cint)) (fun pid ->
        GenLow.returnGen (cid, pid))
    | None -> GenLow.returnGen (cid, 1))

(** val convert_program_interface : prog_int0 -> Program.interface **)

let convert_program_interface pi =
  PMap.fold (fun cid cint acc ->
    let (lexp, limp) = cint in
    setm nat_ordType acc (Obj.magic Coq_Pos.to_nat cid) { Component.export =
      (list2fset nat_ordType (map (Obj.magic Coq_Pos.to_nat) lexp));
      Component.import =
      (list2fset (prod_ordType nat_ordType nat_ordType)
        (map (fun pat ->
          let (c, p) = pat in
          Obj.magic ((Coq_Pos.to_nat c), (Coq_Pos.to_nat p))) limp)) }) pi
    (emptym nat_ordType)

(** val convert_procedures : code PMap.t PMap.t -> code nMap nMap **)

let convert_procedures all =
  PMap.fold (fun cid pm acc ->
    setm nat_ordType acc (Obj.magic Coq_Pos.to_nat cid)
      (PMap.fold (fun pid pcode acc1 ->
        setm nat_ordType acc1 (Obj.magic Coq_Pos.to_nat pid) pcode) pm
        (emptym nat_ordType))) all (emptym nat_ordType)

(** val convert_buffers :
    (int * (int, value list) sum) list PMap.t -> (int * (int, value list)
    sum) list FMap.fmap_type **)

let convert_buffers buffs =
  PMap.fold (fun cid b acc ->
    setm nat_ordType acc (Obj.magic Coq_Pos.to_nat cid)
      (map (fun pat -> let (id0, s) = pat in ((Coq_Pos.to_nat id0), s)) b))
    buffs (emptym nat_ordType)

(** val fix_main :
    code PMap.t PMap.t -> component_id -> procedure_id -> instr list PMap.t
    PMap.t **)

let fix_main all cid pid =
  match PMap.find cid all with
  | Some pmap ->
    (match PMap.find pid pmap with
     | Some l ->
       PMap.add cid
         (PMap.add pid
           (map (fun i -> match i with
                          | IReturn -> IHalt
                          | _ -> i) l) pmap) all
     | None -> all)
  | None -> all

(** val genIntermediateProgram :
    test_type -> Intermediate.program GenLow.coq_G **)

let genIntermediateProgram t1 =
  GenLow.bindGen
    (GenLow.choose chooseNat ((Pervasives.succ 0),
      (N.to_nat (N.sub SFI.coq_COMP_MAX 1)))) (fun n ->
    let cids = pos_list n in
    GenLow.bindGen (gen_program_interface cids) (fun pi ->
      GenLow.bindGen (gen_buffers cids) (fun buffers ->
        GenLow.bindGen (gen_procedures t1 pi buffers) (fun procs ->
          GenLow.bindGen (gen_main pi) (fun main ->
            let (mc, mp) = main in
            let fixed_procs = fix_main procs mc mp in
            GenLow.returnGen { Intermediate.prog_interface =
              (convert_program_interface pi); Intermediate.prog_procedures =
              (convert_procedures fixed_procs); Intermediate.prog_buffers =
              (convert_buffers buffers); Intermediate.prog_main = (Some
              ((Coq_Pos.to_nat mc), (Coq_Pos.to_nat mp))) })))))

(** val fUEL : int **)

let fUEL =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val run_intermediate_program :
    Intermediate.program -> (trace * Coq_CS.state) execution_state **)

let run_intermediate_program ip =
  runp fUEL ip

type store_log_entry =
  (RiscMachine.pc * RiscMachine.address) * RiscMachine.value

type store_log = store_log_entry list * RiscMachine.address list

(** val update_store_log :
    Env.t -> MachineState.t -> trace -> MachineState.t -> store_log ->
    store_log_entry list * RiscMachine.address list **)

let update_store_log _ st _ _ log =
  let (p, regs) = st in
  let (mem1, pc0) = p in
  let (st_log, addr_log) = log in
  let nlog =
    if (=) (count_occ N.eq_dec addr_log pc0) 0
    then app addr_log (pc0 :: [])
    else addr_log
  in
  (match RiscMachine.Memory.get_word mem1 pc0 with
   | Some w ->
     (match w with
      | RiscMachine.Data _ -> (st_log, nlog)
      | RiscMachine.Instruction instr0 ->
        (match instr0 with
         | RiscMachine.ISA.IStore (rptr, _) ->
           (match RiscMachine.RegisterFile.get_register rptr regs with
            | Some ptr ->
              let addr = RiscMachine.Memory.to_address ptr in
              (match RiscMachine.RegisterFile.get_register
                       RiscMachine.Register.coq_R_SFI_SP regs with
               | Some sp -> ((app st_log (((pc0, addr), sp) :: [])), nlog)
               | None -> (st_log, nlog))
            | None -> (st_log, nlog))
         | _ -> (st_log, nlog)))
   | None -> (st_log, nlog))

(** val show_log_entry : store_log_entry -> char list **)

let show_log_entry = function
| (p, sfi_sp) ->
  let (pc0, addr) = p in
  append ('p'::('c'::(':'::(' '::[]))))
    (append (show_addr pc0)
      (append (' '::('p'::('t'::('r'::(':'::(' '::[]))))))
        (append (show_addr addr)
          (append
            (' '::('s'::('f'::('i'::(' '::('s'::('p'::(':'::(' '::[])))))))))
            (show0 showInt sfi_sp)))))

type store_stat =
  (((int * int) * int) * (trace * Coq_CS.state) execution_state) * int

(** val show_store_stat : store_stat show **)

let show_store_stat = function
| (y, si) ->
  let (y0, es) = y in
  let (y1, e1) = y0 in
  let (steps, i) = y1 in
  append (show0 show_Component_id steps)
    (append (','::[])
      (append (show0 show_Component_id si)
        (append (','::[])
          (append (show0 show_Component_id i)
            (append (','::[])
              (append (show0 show_Component_id e1)
                (append (','::[]) (show0 show_ip_exec_state es))))))))

(** val store_stats :
    store_log -> int -> (trace * Coq_CS.state) execution_state -> store_stat **)

let store_stats log steps es =
  let (l1, l2) = log in
  let i =
    length
      (filter (fun pat ->
        let (y, _) = pat in
        let (pc0, addr) = y in SFI.is_same_component_bool pc0 addr) l1)
  in
  ((((steps, i), (sub (length l1) i)), es), (length l2))

(** val eval_store_program :
    sfi_program -> ((trace * MachineState.t) * int) either * store_log **)

let eval_store_program p =
  CS.eval_program_with_state update_store_log fUEL p
    RiscMachine.RegisterFile.reset_all ([], [])

(** val store_checker :
    store_log -> int -> (trace * Coq_CS.state) execution_state -> checker **)

let store_checker log steps es =
  let (l1, _) = log in
  collect show_store_stat testChecker (store_stats log steps es)
    (match l1 with
     | [] -> checker0 testUnit ()
     | _ :: _ ->
       conjoin
         (map (fun pat ->
           let (y, sfi_sp) = pat in
           let (pc0, addr) = y in
           if SFI.is_same_component_bool pc0 addr
           then checker0 testBool true
           else if N.eqb (SFI.coq_C_SFI addr) SFI.coq_MONITOR_COMPONENT_ID
                then whenFail testBool
                       (append
                         ('F'::('a'::('i'::('l'::('e'::('d'::(' '::('a'::('t'::(':'::(' '::[])))))))))))
                         (show_log_entry ((pc0, addr), sfi_sp)))
                       (N.eqb addr
                         (SFI.address_of SFI.coq_MONITOR_COMPONENT_ID
                           (Z.to_N (Z.add (Z.mul ((fun p->2*p) 1) sfi_sp) 1))
                           0))
                else whenFail testBool
                       (append
                         ('F'::('a'::('i'::('l'::('e'::('d'::(' '::('a'::('t'::(':'::(' '::[])))))))))))
                         (show_log_entry ((pc0, addr), sfi_sp))) false) l1))

(** val store_correct : test_type -> comp_flags -> checker **)

let store_correct t1 cf =
  forAllShrink testChecker show_intermediate_program
    (genIntermediateProgram t1) (shrink0 shrinkIntermediateProgram)
    (fun ip ->
    match compile_program cf ip with
    | Right p ->
      let (res, log) = eval_store_program p in
      let es = run_intermediate_program ip in
      (match es with
       | Wrong (_, _, e1) ->
         (match e1 with
          | InvalidEnv ->
            if dEBUG
            then whenFail testBool
                   (append (show0 show_ip_exec_state es)
                     (show0 show_intermediate_program ip)) false
            else checker0 testUnit ()
          | _ ->
            (match res with
             | Right0 p0 ->
               let (p1, steps) = p0 in
               let (_, t2) = p1 in
               let (p2, _) = t2 in
               let (mem1, _) = p2 in
               whenFail testChecker
                 (append
                   ('m'::('e'::('m'::('o'::('r'::('y'::(' '::('o'::('f'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::(' '::('p'::('r'::('o'::('g'::('r'::('a'::('m'::(':'::(' '::[]))))))))))))))))))))))))))
                   (show_mem mem1)) (store_checker log steps es)
             | Left0 (msg, err) ->
               whenFail testChecker (append msg (show0 show_exec_error err))
                 (store_checker log 0 es)))
       | _ ->
         (match res with
          | Right0 p0 ->
            let (p1, steps) = p0 in
            let (_, t2) = p1 in
            let (p2, _) = t2 in
            let (mem1, _) = p2 in
            whenFail testChecker
              (append
                ('m'::('e'::('m'::('o'::('r'::('y'::(' '::('o'::('f'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::(' '::('p'::('r'::('o'::('g'::('r'::('a'::('m'::(':'::(' '::[]))))))))))))))))))))))))))
                (show_mem mem1)) (store_checker log steps es)
          | Left0 (msg, err) ->
            whenFail testChecker (append msg (show0 show_exec_error err))
              (store_checker log 0 es)))
    | Left (msg, err) ->
      whenFail testBool
        (append
          ('C'::('o'::('m'::('p'::('i'::('l'::('a'::('t'::('i'::('o'::('n'::(' '::('e'::('r'::('r'::('o'::('r'::(':'::(' '::[])))))))))))))))))))
          (append msg (append newline (show0 show_compiler_error err)))) false)

type jump_type =
| Indirect of RiscMachine.Register.t
| Direct

(** val show_jump_type : jump_type show **)

let show_jump_type = function
| Indirect r -> append ('J'::('m'::('p'::(' '::[])))) (show0 show_reg r)
| Direct -> 'J'::('a'::('l'::[]))

type jump_log_entry =
  ((RiscMachine.pc * RiscMachine.address) * jump_type) * trace

type jump_log = jump_log_entry list * RiscMachine.address list

(** val update_jump_log :
    Env.t -> MachineState.t -> trace -> MachineState.t -> jump_log ->
    jump_log_entry list * RiscMachine.address list **)

let update_jump_log _ st t1 _ log =
  let (p, regs) = st in
  let (mem1, pc0) = p in
  let (j_log, addr_log) = log in
  let nlog =
    if (=) (count_occ N.eq_dec addr_log pc0) 0
    then app addr_log (pc0 :: [])
    else addr_log
  in
  (match RiscMachine.Memory.get_word mem1 pc0 with
   | Some w ->
     (match w with
      | RiscMachine.Data _ -> (j_log, nlog)
      | RiscMachine.Instruction instr0 ->
        (match instr0 with
         | RiscMachine.ISA.IJump r ->
           if (||) (N.eqb r RiscMachine.Register.coq_R_RA)
                (N.eqb r RiscMachine.Register.coq_R_T)
           then (match RiscMachine.RegisterFile.get_register r regs with
                 | Some ptr ->
                   ((app j_log ((((pc0, (RiscMachine.Memory.to_address ptr)),
                      (Indirect r)), t1) :: [])), nlog)
                 | None -> (j_log, nlog))
           else (j_log, nlog)
         | RiscMachine.ISA.IJal addr ->
           ((app j_log ((((pc0, addr), Direct), t1) :: [])), nlog)
         | _ -> (j_log, nlog)))
   | None -> (j_log, nlog))

(** val show_jump_log_entry : jump_log_entry -> char list **)

let show_jump_log_entry = function
| (p, t1) ->
  let (p0, type0) = p in
  let (pc0, addr) = p0 in
  append ('p'::('c'::(':'::(' '::[]))))
    (append (show0 show_reg pc0)
      (append (' '::('p'::('t'::('r'::(':'::(' '::[]))))))
        (append (show0 show_reg addr)
          (append (' '::('t'::('y'::('p'::('e'::(':'::(' '::[])))))))
            (append
              (match type0 with
               | Indirect r ->
                 append ('J'::('m'::('p'::(' '::[])))) (show0 show_reg r)
               | Direct -> 'J'::('a'::('l'::[])))
              (append
                (' '::('t'::('r'::('a'::('c'::('e'::(':'::(' '::[]))))))))
                (show0 show_trace t1)))))))

(** val eval_jump_program :
    sfi_program -> ((trace * MachineState.t) * int) either * jump_log **)

let eval_jump_program p =
  CS.eval_program_with_state update_jump_log fUEL p
    RiscMachine.RegisterFile.reset_all ([], [])

type jump_stat =
  (((int * int) * int) * (trace * Coq_CS.state) execution_state) * int

(** val show_jump_stat : jump_stat show **)

let show_jump_stat = function
| (y, si) ->
  let (y0, es) = y in
  let (y1, e1) = y0 in
  let (steps, i) = y1 in
  append (show0 show_Component_id steps)
    (append (','::[])
      (append (show0 show_Component_id si)
        (append (','::[])
          (append (show0 show_Component_id i)
            (append (','::[])
              (append (show0 show_Component_id e1)
                (append (','::[]) (show0 show_ip_exec_state es))))))))

(** val jump_stats :
    jump_log -> int -> (trace * Coq_CS.state) execution_state -> jump_stat **)

let jump_stats log steps es =
  let (l1, l2) = log in
  let i =
    length
      (filter (fun pat ->
        let (y, _) = pat in
        let (y0, _) = y in
        let (pc0, addr) = y0 in
        (||)
          ((||) (SFI.is_same_component_bool pc0 addr)
            (N.eqb (SFI.coq_C_SFI addr) SFI.coq_MONITOR_COMPONENT_ID))
          (N.eqb (SFI.coq_C_SFI pc0) SFI.coq_MONITOR_COMPONENT_ID)) l1)
  in
  let e1 =
    length
      (filter (fun pat ->
        let (y, _) = pat in
        let (y0, _) = y in
        let (pc0, addr) = y0 in
        negb
          ((||)
            ((||) (SFI.is_same_component_bool pc0 addr)
              (N.eqb (SFI.coq_C_SFI addr) SFI.coq_MONITOR_COMPONENT_ID))
            (N.eqb (SFI.coq_C_SFI pc0) SFI.coq_MONITOR_COMPONENT_ID))) l1)
  in
  ((((steps, i), e1), es), (length l2))

(** val jump_checker :
    jump_log -> int -> (trace * Coq_CS.state) execution_state -> checker **)

let jump_checker log steps es =
  let (l1, _) = log in
  collect show_jump_stat testChecker (jump_stats log steps es)
    (match l1 with
     | [] -> checker0 testUnit ()
     | _ :: _ ->
       conjoin
         (map (fun pat ->
           let (y, t1) = pat in
           let (y0, type0) = y in
           let (pc0, addr) = y0 in
           if N.eqb (SFI.coq_C_SFI addr) SFI.coq_MONITOR_COMPONENT_ID
           then checker0 testBool true
           else if N.eqb (SFI.coq_C_SFI pc0) SFI.coq_MONITOR_COMPONENT_ID
                then checker0 testBool true
                else if SFI.is_same_component_bool pc0 addr
                     then (match t1 with
                           | [] ->
                             whenFail testBool
                               (append
                                 ('R'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::(' '::('R'::('_'::('T'::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('i'::('n'::(' '::('i'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::(' '::('j'::('u'::('m'::('p'::('s'::(' '::[]))))))))))))))))))))))))))))))))))))))))
                                 (show0 show_jump_type type0))
                               (match type0 with
                                | Indirect r ->
                                  RiscMachine.Register.eqb
                                    RiscMachine.Register.coq_R_T r
                                | Direct -> true)
                           | _ :: _ ->
                             whenFail testBool
                               (append
                                 ('U'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('c'::('t'::('e'::('d'::(' '::('e'::('v'::('e'::('n'::('t'::(' '::('a'::('t'::(' '::('l'::('o'::('g'::(' '::('e'::('n'::('t'::('r'::('y'::(':'::[])))))))))))))))))))))))))))))))))
                                 (show_jump_log_entry (((pc0, addr), type0),
                                   t1))) false)
                     else (match t1 with
                           | [] ->
                             whenFail testBool
                               (append
                                 ('U'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('c'::('t'::('e'::('d'::(' '::('e'::('m'::('p'::('t'::('y'::(' '::('e'::('v'::('e'::('n'::('t'::(' '::('a'::('t'::(' '::('l'::('o'::('g'::(' '::('e'::('n'::('t'::('r'::('y'::(':'::[])))))))))))))))))))))))))))))))))))))))
                                 (show_jump_log_entry (((pc0, addr), type0),
                                   t1))) false
                           | _ :: _ ->
                             whenFail testBool
                               (append
                                 ('R'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::(' '::('R'::('_'::('A'::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('i'::('n'::(' '::('i'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::(' '::('j'::('u'::('m'::('p'::('s'::(' '::[]))))))))))))))))))))))))))))))))))))))))
                                 (show0 show_jump_type type0))
                               (match type0 with
                                | Indirect r ->
                                  RiscMachine.Register.eqb
                                    RiscMachine.Register.coq_R_RA r
                                | Direct -> true))) l1))

(** val jump_correct : test_type -> comp_flags -> checker **)

let jump_correct _ cf =
  forAllShrink testChecker show_intermediate_program
    (genIntermediateProgram TJump) (shrink0 shrinkIntermediateProgram)
    (fun ip ->
    match compile_program cf ip with
    | Right p ->
      let (res, log) = eval_jump_program p in
      let es = run_intermediate_program ip in
      (match es with
       | Wrong (_, _, e1) ->
         (match e1 with
          | InvalidEnv ->
            if dEBUG
            then whenFail testBool
                   (append (show0 show_ip_exec_state es)
                     (show0 show_intermediate_program ip)) false
            else checker0 testUnit ()
          | _ ->
            (match res with
             | Right0 p0 -> let (_, steps) = p0 in jump_checker log steps es
             | Left0 (msg, err) ->
               whenFail testChecker (append msg (show0 show_exec_error err))
                 (jump_checker log 0 es)))
       | _ ->
         (match res with
          | Right0 p0 -> let (_, steps) = p0 in jump_checker log steps es
          | Left0 (msg, err) ->
            whenFail testChecker (append msg (show0 show_exec_error err))
              (jump_checker log 0 es)))
    | Left (msg, err) ->
      whenFail testBool
        (append
          ('C'::('o'::('m'::('p'::('i'::('l'::('a'::('t'::('i'::('o'::('n'::(' '::('e'::('r'::('r'::('o'::('r'::(':'::(' '::[])))))))))))))))))))
          (append msg (append newline (show0 show_compiler_error err)))) false)

type stack_op =
| Push
| Pop

type cs_log_entry =
  ((RiscMachine.pc * RiscMachine.address) * stack_op) * RiscMachine.ISA.instr

type cs_log = cs_log_entry list * RiscMachine.address list

(** val update_cs_log :
    Env.t -> MachineState.t -> trace -> MachineState.t -> cs_log ->
    cs_log_entry list * RiscMachine.address list **)

let update_cs_log _ st _ st' log =
  let (p, regs) = st in
  let (mem1, pc0) = p in
  let (cs_log0, addr_log) = log in
  let nlog =
    if (=) (count_occ N.eq_dec addr_log pc0) 0
    then app addr_log (pc0 :: [])
    else addr_log
  in
  (match RiscMachine.Memory.get_word mem1 pc0 with
   | Some w ->
     (match w with
      | RiscMachine.Data _ -> (cs_log0, nlog)
      | RiscMachine.Instruction instr0 ->
        (match instr0 with
         | RiscMachine.ISA.IJump r ->
           (match RiscMachine.RegisterFile.get_register r regs with
            | Some ptr ->
              let addr = RiscMachine.Memory.to_address ptr in
              if SFI.is_same_component_bool pc0 addr
              then (cs_log0, nlog)
              else ((app cs_log0 ((((pc0, addr), Pop), instr0) :: [])), nlog)
            | None -> (cs_log0, nlog))
         | RiscMachine.ISA.IJal addr ->
           if SFI.is_same_component_bool pc0 addr
           then (cs_log0, nlog)
           else let (_, regs') = st' in
                (match RiscMachine.RegisterFile.get_register
                         RiscMachine.Register.coq_R_RA regs' with
                 | Some addr0 ->
                   ((app cs_log0 ((((pc0,
                      (RiscMachine.Memory.to_address addr0)), Push),
                      instr0) :: [])), nlog)
                 | None -> (cs_log0, nlog))
         | _ -> (cs_log0, nlog)))
   | None -> (cs_log0, nlog))

(** val eval_cs_program :
    sfi_program -> ((trace * MachineState.t) * int) either * cs_log **)

let eval_cs_program p =
  CS.eval_program_with_state update_cs_log fUEL p
    RiscMachine.RegisterFile.reset_all ([], [])

type cs_stat = ((int * int) * (trace * Coq_CS.state) execution_state) * int

(** val show_cs_stat : cs_stat show **)

let show_cs_stat = function
| (y, si) ->
  let (y0, es) = y in
  let (steps, op0) = y0 in
  append (show0 show_Component_id steps)
    (append (','::[])
      (append (show0 show_Component_id si)
        (append (','::[])
          (append (show0 show_Component_id op0)
            (append (','::[]) (show0 show_ip_exec_state es))))))

(** val cs_stats :
    cs_log -> int -> (trace * Coq_CS.state) execution_state -> cs_stat **)

let cs_stats log steps es =
  let (l1, l2) = log in (((steps, (length l1)), es), (length l2))

(** val cs_checker :
    cs_log -> int -> (trace * Coq_CS.state) execution_state -> checker **)

let cs_checker log steps es =
  let (l1, _) = log in
  let aux =
    let rec aux l s =
      match l with
      | [] -> checker0 testBool true
      | y :: xs ->
        let (y0, instr0) = y in
        let (y1, op0) = y0 in
        let (pc0, addr) = y1 in
        (match op0 with
         | Push -> aux xs (addr :: s)
         | Pop ->
           (match s with
            | [] ->
              whenFail testBool
                (append
                  ('A'::('t'::('t'::('e'::('m'::('t'::('i'::('n'::('g'::(' '::('t'::('o'::(' '::('p'::('o'::('p'::(' '::('f'::('r'::('o'::('m'::(' '::('e'::('m'::('p'::('t'::('y'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('a'::('t'::(' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::[]))))))))))))))))))))))))))))))))))))))))))))
                  (show0 show_reg pc0)) false
            | a :: s' ->
              if N.eqb a addr
              then aux xs s'
              else whenFail testBool
                     (append
                       ('A'::('t'::('t'::('e'::('m'::('t'::('i'::('n'::('g'::(' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::(' '::('o'::('n'::(' '::('t'::('h'::('e'::(' '::('s'::('t'::('a'::('c'::('k'::(':'::(' '::[]))))))))))))))))))))))))))))))))
                       (append (show_addr a)
                         (append
                           (' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::(' '::('i'::('n'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::(':'::(' '::[]))))))))))))))))))))))
                           (append (show_addr addr)
                             (append
                               ('a'::('t'::(' '::('p'::('c'::(':'::(' '::[])))))))
                               (append (show_addr pc0)
                                 (append
                                   (' '::('i'::('n'::('s'::('t'::('r'::(':'::(' '::[]))))))))
                                   (show0 show_instr instr0)))))))) false))
    in aux
  in
  collect show_cs_stat testChecker (cs_stats log steps es)
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> checker0 testBool false)
       (fun _ ->
       match l1 with
       | [] -> checker0 testUnit ()
       | _ :: _ -> aux l1 [])
       steps)

(** val cs_correct : test_type -> comp_flags -> checker **)

let cs_correct t1 cf =
  forAllShrink testChecker show_intermediate_program
    (genIntermediateProgram t1) (shrink0 shrinkIntermediateProgram)
    (fun ip ->
    match compile_program cf ip with
    | Right p ->
      let (res, log) = eval_cs_program p in
      let es = run_intermediate_program ip in
      (match es with
       | Wrong (_, _, e1) ->
         (match e1 with
          | InvalidEnv ->
            if dEBUG
            then whenFail testBool
                   (append (show0 show_ip_exec_state es)
                     (show0 show_intermediate_program ip)) false
            else checker0 testUnit ()
          | _ ->
            (match res with
             | Right0 p0 ->
               let (p1, steps) = p0 in
               let (_, t2) = p1 in
               let (p2, _) = t2 in
               let (mem1, _) = p2 in
               whenFail testChecker
                 (append
                   ('m'::('e'::('m'::('o'::('r'::('y'::(' '::('o'::('f'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::(' '::('p'::('r'::('o'::('g'::('r'::('a'::('m'::(':'::(' '::[]))))))))))))))))))))))))))
                   (show_mem mem1)) (cs_checker log steps es)
             | Left0 (msg, err) ->
               whenFail testChecker (append msg (show0 show_exec_error err))
                 (cs_checker log 0 es)))
       | _ ->
         (match res with
          | Right0 p0 ->
            let (p1, steps) = p0 in
            let (_, t2) = p1 in
            let (p2, _) = t2 in
            let (mem1, _) = p2 in
            whenFail testChecker
              (append
                ('m'::('e'::('m'::('o'::('r'::('y'::(' '::('o'::('f'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::(' '::('p'::('r'::('o'::('g'::('r'::('a'::('m'::(':'::(' '::[]))))))))))))))))))))))))))
                (show_mem mem1)) (cs_checker log steps es)
          | Left0 (msg, err) ->
            whenFail testChecker (append msg (show0 show_exec_error err))
              (cs_checker log 0 es)))
    | Left (msg, err) ->
      whenFail testBool
        (append
          ('C'::('o'::('m'::('p'::('i'::('l'::('a'::('t'::('i'::('o'::('n'::(' '::('e'::('r'::('r'::('o'::('r'::(':'::(' '::[])))))))))))))))))))
          (append msg (append newline (show0 show_compiler_error err)))) false)

type correct_log = trace * RiscMachine.address list

(** val update_correct_log :
    Env.t -> MachineState.t -> trace -> MachineState.t -> correct_log ->
    trace * RiscMachine.address list **)

let update_correct_log g st _ _ log =
  let (p, regs) = st in
  let (mem1, pc0) = p in
  let (c_log, addr_log) = log in
  let nlog =
    if (=) (count_occ N.eq_dec addr_log pc0) 0
    then app addr_log (pc0 :: [])
    else addr_log
  in
  (match RiscMachine.Memory.get_word mem1 pc0 with
   | Some w ->
     (match w with
      | RiscMachine.Data _ -> (c_log, nlog)
      | RiscMachine.Instruction instr0 ->
        (match instr0 with
         | RiscMachine.ISA.IJump reg ->
           (match RiscMachine.RegisterFile.get_register reg regs with
            | Some addr ->
              let pc' = RiscMachine.Memory.to_address addr in
              if SFI.is_same_component_bool pc0 pc'
              then (c_log, nlog)
              else if N.eqb (SFI.coq_C_SFI pc') SFI.coq_MONITOR_COMPONENT_ID
                   then (c_log, nlog)
                   else (match RiscMachine.RegisterFile.get_register
                                 RiscMachine.Register.coq_R_COM regs with
                         | Some rcomval ->
                           (match Env.get_component_name_from_id
                                    (SFI.coq_C_SFI pc0) g with
                            | Some cpc ->
                              (match Env.get_component_name_from_id
                                       (SFI.coq_C_SFI pc') g with
                               | Some cpc' ->
                                 ((app c_log ((ERet (cpc, rcomval,
                                    cpc')) :: [])), nlog)
                               | None -> (c_log, nlog))
                            | None -> (c_log, nlog))
                         | None -> (c_log, nlog))
            | None -> (c_log, nlog))
         | RiscMachine.ISA.IJal addr ->
           if SFI.is_same_component_bool pc0 addr
           then (c_log, nlog)
           else if N.eqb (SFI.coq_C_SFI pc0) SFI.coq_MONITOR_COMPONENT_ID
                then (c_log, nlog)
                else let ot = CS.call_trace g pc0 addr regs in
                     (match ot with
                      | Some t1 -> ((app c_log t1), nlog)
                      | None -> (c_log, nlog))
         | _ -> (c_log, nlog)))
   | None -> (c_log, nlog))

type correct_stat =
  (((int * int) * int) * (trace * Coq_CS.state) execution_state) * int

(** val show_correct_stat : correct_stat show **)

let show_correct_stat = function
| (y, si) ->
  let (y0, es) = y in
  let (y1, t1) = y0 in
  let (steps, i) = y1 in
  append (show0 show_Component_id steps)
    (append (','::[])
      (append (show0 show_Component_id si)
        (append (','::[])
          (append (show0 show_Component_id i)
            (append (','::[])
              (append (show0 show_Component_id t1)
                (append (','::[]) (show0 show_ip_exec_state es))))))))

(** val correct_stats :
    correct_log -> int -> (trace * Coq_CS.state) execution_state -> trace ->
    correct_stat **)

let correct_stats log steps es intermTrace =
  let (l1, l2) = log in
  ((((steps, (length intermTrace)), (length l1)), es), (length l2))

(** val eval_correct_program :
    int -> sfi_program -> ((trace * MachineState.t) * int)
    either * correct_log **)

let eval_correct_program fuel p =
  CS.eval_program_with_state update_correct_log fuel p
    RiscMachine.RegisterFile.reset_all ([], [])

(** val event_eqb : event -> event -> bool **)

let event_eqb e1 e2 =
  match e1 with
  | ECall (c1, p1, _, c1') ->
    (match e2 with
     | ECall (c2, p2, _, c2') ->
       (&&) ((&&) (Component.eqb c1 c2) (Procedure.eqb p1 p2))
         (Component.eqb c1' c2')
     | ERet (_, _, _) -> false)
  | ERet (c1, _, c1') ->
    (match e2 with
     | ECall (_, _, _, _) -> false
     | ERet (c2, _, c2') -> (&&) (Component.eqb c1 c2) (Component.eqb c1' c2'))

(** val sublist : trace -> trace -> bool **)

let rec sublist l1 l2 =
  match l1 with
  | [] -> true
  | x :: xs1 ->
    (match l2 with
     | [] -> false
     | y :: xs2 -> if event_eqb x y then sublist xs1 xs2 else false)

(** val correct_checker :
    correct_log -> int -> (trace * Coq_CS.state) execution_state -> trace ->
    checker **)

let correct_checker log steps es intermTrace =
  let (l1, _) = log in
  collect show_correct_stat testChecker
    (correct_stats log steps es intermTrace)
    (checker0 testBool (sublist intermTrace l1))

(** val compiler_correct : test_type -> int -> comp_flags -> checker **)

let compiler_correct t1 fuel cf =
  forAllShrink testChecker show_intermediate_program
    (genIntermediateProgram t1) (shrink0 shrinkIntermediateProgram)
    (fun ip ->
    match compile_program cf ip with
    | Right p ->
      let (target_res, log) = eval_correct_program fuel p in
      let interm_res = runp fuel ip in
      (match interm_res with
       | OutOfFuel _ -> checker0 testUnit ()
       | _ ->
         (match interm_res with
          | Wrong (_, _, e1) ->
            (match e1 with
             | InvalidEnv ->
               if dEBUG
               then whenFail testBool
                      (append (show0 show_ip_exec_state interm_res)
                        (show0 show_intermediate_program ip)) false
               else checker0 testUnit ()
             | _ ->
               let interm_trace =
                 match interm_res with
                 | Running p0 -> let (tr, _) = p0 in tr
                 | OutOfFuel p0 -> let (tr, _) = p0 in tr
                 | Halted tr -> tr
                 | Wrong (tr, _, _) -> tr
               in
               (match target_res with
                | Right0 p0 ->
                  let (p1, steps) = p0 in
                  let (t2, t3) = p1 in
                  let (p2, _) = t3 in
                  let (mem1, _) = p2 in
                  if (=) steps fuel
                  then checker0 testUnit ()
                  else whenFail testChecker
                         (append
                           ('i'::('n'::('t'::('e'::('r'::('m'::('e'::('d'::('i'::('a'::('t'::('e'::(' '::('t'::('r'::('a'::('c'::('e'::(':'::(' '::[]))))))))))))))))))))
                           (append (show0 show_trace interm_trace)
                             (append
                               (' '::('t'::('a'::('r'::('g'::('e'::('t'::(' '::('t'::('r'::('a'::('c'::('e'::(' '::('l'::('o'::('g'::(':'::[]))))))))))))))))))
                               (append (show0 show_trace (fst log))
                                 (append newline
                                   (append
                                     (' '::('t'::('a'::('r'::('g'::('e'::('t'::(' '::('t'::('r'::('a'::('c'::('e'::(' '::('t'::(':'::[]))))))))))))))))
                                     (append (show0 show_trace t2)
                                       (append newline
                                         (append
                                           ('i'::('n'::('t'::('e'::('r'::('m'::('e'::('d'::('i'::('a'::('t'::('e'::(' '::('p'::('r'::('o'::('g'::('r'::('a'::('m'::(':'::(' '::(':'::[])))))))))))))))))))))))
                                           (append
                                             (show0 show_intermediate_program
                                               ip)
                                             (append newline
                                               (append
                                                 ('m'::('e'::('m'::('o'::('r'::('y'::(' '::('o'::('f'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::(' '::('p'::('r'::('o'::('g'::('r'::('a'::('m'::(':'::(' '::[]))))))))))))))))))))))))))
                                                 (show_mem mem1)))))))))))))
                         (correct_checker log steps interm_res interm_trace)
                | Left0 (msg, err) ->
                  whenFail testChecker
                    (append msg (show0 show_exec_error err))
                    (correct_checker log 0 interm_res interm_trace)))
          | _ ->
            let interm_trace =
              match interm_res with
              | Running p0 -> let (tr, _) = p0 in tr
              | OutOfFuel p0 -> let (tr, _) = p0 in tr
              | Halted tr -> tr
              | Wrong (tr, _, _) -> tr
            in
            (match target_res with
             | Right0 p0 ->
               let (p1, steps) = p0 in
               let (t2, t3) = p1 in
               let (p2, _) = t3 in
               let (mem1, _) = p2 in
               if (=) steps fuel
               then checker0 testUnit ()
               else whenFail testChecker
                      (append
                        ('i'::('n'::('t'::('e'::('r'::('m'::('e'::('d'::('i'::('a'::('t'::('e'::(' '::('t'::('r'::('a'::('c'::('e'::(':'::(' '::[]))))))))))))))))))))
                        (append (show0 show_trace interm_trace)
                          (append
                            (' '::('t'::('a'::('r'::('g'::('e'::('t'::(' '::('t'::('r'::('a'::('c'::('e'::(' '::('l'::('o'::('g'::(':'::[]))))))))))))))))))
                            (append (show0 show_trace (fst log))
                              (append newline
                                (append
                                  (' '::('t'::('a'::('r'::('g'::('e'::('t'::(' '::('t'::('r'::('a'::('c'::('e'::(' '::('t'::(':'::[]))))))))))))))))
                                  (append (show0 show_trace t2)
                                    (append newline
                                      (append
                                        ('i'::('n'::('t'::('e'::('r'::('m'::('e'::('d'::('i'::('a'::('t'::('e'::(' '::('p'::('r'::('o'::('g'::('r'::('a'::('m'::(':'::(' '::(':'::[])))))))))))))))))))))))
                                        (append
                                          (show0 show_intermediate_program ip)
                                          (append newline
                                            (append
                                              ('m'::('e'::('m'::('o'::('r'::('y'::(' '::('o'::('f'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::(' '::('p'::('r'::('o'::('g'::('r'::('a'::('m'::(':'::(' '::[]))))))))))))))))))))))))))
                                              (show_mem mem1)))))))))))))
                      (correct_checker log steps interm_res interm_trace)
             | Left0 (msg, err) ->
               whenFail testChecker (append msg (show0 show_exec_error err))
                 (correct_checker log 0 interm_res interm_trace))))
    | Left (msg, err) ->
      whenFail testBool
        (append
          ('C'::('o'::('m'::('p'::('i'::('l'::('a'::('t'::('i'::('o'::('n'::(' '::('e'::('r'::('r'::('o'::('r'::(':'::(' '::[])))))))))))))))))))
          (append msg (append newline (show0 show_compiler_error err)))) false)

type checker_type =
| CStore
| CJump
| CStack
| CCompCorrect

type flag =
| TStoreInstrOff
| TStoreInstr1Off
| TStoreInstr2Off
| TJumpInstrOff
| TJumpInstr1Off
| TJumpInstr2Off
| TPushSfiHaltNotPresent
| TPopSfiNotAligned
| TSetSfiRegistersMissing
| TAfterCallLabelMissing
| TTargetsNotAligned
| TAllOff

(** val get_comp_flag : flag -> comp_flags **)

let get_comp_flag = function
| TStoreInstrOff -> set_store_instr_off
| TStoreInstr1Off -> set_store_instr1_off
| TStoreInstr2Off -> set_store_instr2_off
| TJumpInstrOff -> set_jump_instr_off
| TJumpInstr1Off -> set_jump_instr1_off
| TJumpInstr2Off -> set_jump_instr2_off
| TPushSfiHaltNotPresent -> set_push_sfi_halt_not_present
| TPopSfiNotAligned -> set_pop_sfi_not_aligned
| TSetSfiRegistersMissing -> set_set_sfi_registers_missing
| TAfterCallLabelMissing -> set_after_call_label_missing
| TTargetsNotAligned -> set_targets_not_aligned
| TAllOff -> all_flags_off

(** val run_injection_test : checker_type -> flag -> char list **)

let run_injection_test ct f =
  match ct with
  | CStore ->
    show0 showResult
      (quickCheck testChecker (store_correct TStore (get_comp_flag f)))
  | CJump ->
    show0 showResult
      (quickCheck testChecker (jump_correct TJump (get_comp_flag f)))
  | CStack ->
    show0 showResult
      (quickCheck testChecker (cs_correct TStack (get_comp_flag f)))
  | CCompCorrect ->
    show0 showResult
      (quickCheck testChecker
        (compiler_correct TCompilerCorrect fUEL (get_comp_flag f)))
