(** {1 Non-catenable deques} *)

(** Described in Section 3 of
    {{:http://epubs.siam.org/doi/abs/10.1137/S0097539798339430}
    Kaplan, Okasaki & Tarjan (2000)} (KOT), this data-structure
    implements the deque operations (but not concatenation) in {i
    amortised} constant time, using recursive slowdown and
    lazyness.

    Judging from the letter of the article, KOT does not seem to
    indend use of lazyness in this datastructure, but explicit
    memoisation. Using lazyness is presumably equivalent, and yields a
    simpler implementation. Since simplicity is the motto of KOT,
    lazyness is used here. *)


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
    nested) inductive types whose recursive occurrence is kept lazy so
    that recursive calls can be staged. See
    {{:http://www.cambridge.org/fr/academic/subjects/computer-science/programming-languages-and-applied-logic/purely-functional-data-structures?format=PB}
    {i Purely functional datastructures}}, Okasaki (1999) for more on
    the use of lazyness to obtain amortised complexity in presence of
    immutable data structures.

    Non-nested non-uniform data-structure such as this one are
    typically efficient for deque operations as well as random access,
    but have poor concatenation properties.

    In KOT, prefixes and suffixes which are full or empty are called
    {i red}, the other ones are called {i green}. Dedicated functions
    turn red prefixes and suffixes into green ones so that deque
    operations can be applied. *)
type 'a t =
  | Empty
  | Q of 'a Prefix.t * ('a*'a) t Lazy.t * 'a Suffix.t


(** {6 Push}*)

(** The deque operations on this data structure are mostly symmetric,
    so understanding [push] is sufficient to understand all four
    operations.

    In KOT there is a function to turn red prefixes green to prepare
    for a [push] or a [pop] (and a respective one to turn red suffixes
    green). In this implementation we will inline the calls to the
    preparatory function: it is a very simple function, and the code
    is, in fact, shorter and easier to read this way. *)

(** The type annotation on the [push] function is necessary because
    the recursion is non-uniform: the recursive call to [push] is on a
    deque of type [('a*'a) t]. *)
let rec push : 'a. 'a -> 'a t -> 'a t = fun x d ->
  match d with
  | Q (Prefix.Three(y,z,w),c,s) ->
      Q( Prefix.Two (x,y) ,
         lazy (push (y,z) (Lazy.force c)) ,
         s )
  | Q(p,c,s) ->
      Q( Prefix.push x p ,
         c ,
         s )
  | Empty ->
      Q( Prefix.One x ,
         Lazy.from_val Empty ,
         Suffix.Zero )


(** {6 Pop} *)

(** {!pop} is a partial function (empty queues cannot be
    popped). Partiality is modeled with an exception. *)
exception CannotPop

(** The [pop] operation needs to force the child deque when the prefix
    is empty. This is where sharing is achieved between copies: if a big
    deque is copied, both copies will share the potentially long
    computation of running the successive [push]-s and [inject]-s in order
    to expose the front pair of the child deque. *)
let rec pop : 'a. 'a t -> ('a*'a t) = function
  | Q(Prefix.Zero,lazy Empty,Suffix.One x) ->
      (** Ensures that empty deques are inded represented by
          {!Empty}. *)
      x , Empty
  | Q(Prefix.Zero,lazy Empty,s) ->
      (** The precondition to {!Suffix.pop} is always verified: empty
          deques are represented by {!Empty}*)
      let (x,s') = Suffix.pop s in
      x , Q( Prefix.Zero , Lazy.from_val Empty , s' )
  | Q(Prefix.Zero,lazy c,s) ->
      let ((x,y),c') = pop c in
      x , Q( Prefix.One y , Lazy.from_val c' , s )
  | Q(p,c,s) ->
      let (x,p') = Prefix.pop p in
      x , Q( p' , c , s )
  | Empty -> raise CannotPop


(** {6 Inject} *)

let rec inject : 'a. 'a t -> 'a -> 'a t = fun d x ->
  match d with
  | Q (p,c,Suffix.Three(y,z,w)) ->
      Q( p ,
         lazy (inject (Lazy.force c) (y,z)) ,
         Suffix.Two (x,y) )
  | Q(p,c,s) ->
      Q( p ,
         c ,
         Suffix.inject s x )
  | Empty ->
      Q( Prefix.Zero ,
         Lazy.from_val Empty ,
         Suffix.One x )


(** {6 Eject} *)

exception CannotEject

let rec eject : 'a. 'a t -> ('a t * 'a) = function
  | Q(Prefix.One x,lazy Empty,Suffix.Zero) ->
      (** Ensures that empty deques are inded represented by
          {!Empty}. *)
      Empty , x
  | Q(p,lazy Empty,Suffix.Zero) ->
      (** The precondition to {!Suffix.pop} is always verified: empty
          deques are represented by {!Empty}*)
      let (p',x) = Prefix.eject p in
      Q( p' , Lazy.from_val Empty , Suffix.Zero ) , x
  | Q(p,lazy c,Suffix.Zero) ->
      let (c',(x,y)) = eject c in
      Q( p , Lazy.from_val c' , Suffix.One x ) , y
  | Q(p,c,s) ->
      let (s',x) = Suffix.eject s in
      Q( p , c , s' ) , x
  | Empty -> raise CannotEject
