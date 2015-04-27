(** {1 Non-catenable deques with update} *)

(** Described in Section 3.4 of
    {{:http://epubs.siam.org/doi/abs/10.1137/S0097539798339430}
    Kaplan, Okasaki & Tarjan (2000)} (KOT), this data-structure
    implements the deque operation (but not concatenation) in {i
    amortised} constant time, using recursive slowdown and
    updates.

    This data-structure is a variant of that presented in
    {!Section3}. It is slightly more complicated, but the authors deem
    it sligthly more efficient. *)


(** Prefixes are taken to be vectors of size at most 3, which are seen
    as bounded-size deques. Note that because of bounded size, deque
    operations cannot always be performed, so each of the deque
    operations have a precondition, marked here by an [assert false]
    in the forbidden branches. *)
module Prefix = struct

  type 'a t =
    | Zero
    | One of 'a
    | Two of 'a * 'a
    | Three of 'a * 'a * 'a

  let push x = function
    | Zero -> One x
    | One y -> Two (x,y)
    | Two (y,z) -> Three (x,y,z)
    | Three _ -> assert false 

  let pop = function
    | Zero -> assert false
    | One x -> x , Zero
    | Two (x,y) -> x , One y
    | Three (x,y,z) -> x , Two (y,z)

  let inject d z =
    match d with
    | Zero -> One z
    | One y -> Two (y,z)
    | Two (x,y) -> Three (x,y,z)
    | Three _ -> assert false

  let eject = function
    | Zero -> assert false
    | One z -> Zero , z
    | Two (y,z) -> One y , z
    | Three (x,y,z) -> Two (x,y) , z

end


(** Suffixes, for this data-structure, are identical to prefixes (see
    the {!Prefix} module). They are reimplemented here, however, so
    that type errors are more precise. *)
module Suffix = struct

  type 'a t =
    | Zero
    | One of 'a
    | Two of 'a * 'a
    | Three of 'a * 'a * 'a

  let push x = function
    | Zero -> One x
    | One y -> Two (x,y)
    | Two (y,z) -> Three (x,y,z)
    | Three _ -> assert false 

  let pop = function
    | Zero -> assert false
    | One x -> x , Zero
    | Two (x,y) -> x , One y
    | Three (x,y,z) -> x , Two (y,z)

  let inject d z =
    match d with
    | Zero -> One z
    | One y -> Two (y,z)
    | Two (x,y) -> Three (x,y,z)
    | Three _ -> assert false

  let eject = function
    | Zero -> assert false
    | One z -> Zero , z
    | Two (y,z) -> One y , z
    | Three (x,y,z) -> Two (x,y) , z

end


(** This comparatively simple deque is a non-uniform (though not
    nested) inductive types (see also {!Section3}) whose recursive
    occurrence is kept in a reference so that it can be updated to a
    representation of the same list (which preserves persistence) but
    with a representation which is better suited to future deque
    operations.

    In KOT, prefixes and suffixes which are full or empty are called
    {i red}, the other ones are called {i green}. Dedicated functions
    turn red prefixes and suffixes into green ones so that deque
    operations can be applied. The reference is updated at most twice:
    deques with a red prefix (resp. suffix) are turned into an
    equivalent deque with a green prefix (resp. suffix). *)
type 'a t =
  | Empty
  | Q of 'a u
and 'a u = {
  mutable p : 'a Prefix.t ;
  mutable c : ('a*'a) t ;
  mutable s : 'a Suffix.t ;
}

(** {6 Push}*)

(** The deque operations on this data structure are mostly symmetric,
    so understanding [push] is sufficient to understand all four
    operations.

    In KOT there is a single function [gp] to turn red prefixes green
    to prepare for a [push] or a [pop] (and a respective [gs] to turn
    red suffixes green). In this implementation we will split the [gp]
    function into two functions, [gp_push] and [gp_pop], called
    respectively before a [push] and a [pop]. This does not affect the
    algorithm since [gp] (resp. [gd]), in KOT, is actually the
    disjunction of these two function, and in every call, it is
    statically know which branch will be taken. The code ends up
    slightly simplified because [push] and [pop] do not need to be
    mutually recursive. *)

(** The type annotation on the [push] and [gp_push] functions is
    necessary because the recursion is non-uniform: the recursive call
    to [push] inside [gp_push] is on a deque of type [('a*'a) t]. *)
let rec push : 'a. 'a -> 'a t -> 'a t = fun x d ->
  let () = gp_push d in
  match d with
  | Q {p;c;s} -> Q { p=Prefix.push x p ; c ; s }
  | Empty -> Q { p=Prefix.One x ; c=Empty ; s=Suffix.Zero }

and gp_push : 'a. 'a t -> unit = function
  | Q ({p=Prefix.Three(y,z,w);c;s} as q) ->
      q.p <- Prefix.One y;
      q.c <- push (z,w) c
  | d -> ()


(** {6 Pop} *)

(** {!pop} is a partial function (empty queues cannot be
    popped). Partiality is modeled with an exception. *)
exception CannotPop

(** Smart constructor, ensures that empty deques are indeed
    implemented as [Empty]. Used in {!pop} and {!eject}. *)
let q p c s =
  match p , c , s with
  | Prefix.Zero , Empty , Suffix.Zero -> Empty
  | p , c , s -> Q { p ; c ; s }

(** The [pop] operation needs to force the child deque when the prefix
    is empty. This is where sharing is achieved between copies: if a big
    deque is copied, both copies will share the potentially long
    computation of running the successive [push]-s and [inject]-s in order
    to expose the front pair of the child deque. *)
let rec pop : 'a. 'a t -> ('a*'a t) = fun d ->
  let () = gp_pop d in
  match d with
  | Q {p;c;s} ->
      let (x,p') = Prefix.pop p in
      x , q p' c s
  | Empty -> raise CannotPop
and gp_pop : 'a. 'a t -> unit = function
  | Q ({p=Prefix.Zero;c=Empty;s}) ->
      ()
  | Q ({p=Prefix.Zero;c;s} as q) ->
      let ((x,y),c') = pop c in
      q.p <- Prefix.Two(x,y);
      q.c <- c'
  | d -> ()


(** {6 Inject} *)

let rec inject : 'a. 'a t -> 'a -> 'a t = fun d x ->
  let () = gs_inject d in
  match d with
  | Q {p;c;s} -> Q { p ; c ; s=Suffix.inject s x }
  | Empty -> Q { p=Prefix.Zero ; c=Empty ; s=Suffix.One x }
and gs_inject : 'a. 'a t -> unit = function
  | Q ({p;c;s=Suffix.Three(y,z,w)} as q) ->
      q.c <- inject c (y,z);
      q.s <- Suffix.One w
  | d -> ()


(** {6 Eject} *)

exception CannotEject

let rec eject : 'a. 'a t -> ('a t * 'a) = fun d ->
  match d with
  | Q {p;c;s} ->
      let (s',x) = Suffix.eject s in
      q p c s' , x
  | Empty -> raise CannotEject
and gs_eject : 'a. 'a t -> unit = function
  | Q ({p;c=Empty;s=Suffix.Zero}) ->
      ()
  | Q ({p;c;s=Suffix.Zero} as q) ->
      let (c',(x,y)) = eject c in
      q.c <- c';
      q.s <- Suffix.Two(x,y)
  | d -> ()
