(** {1 Catenable steques} *)

(** Described in Section 4 of
    {{:http://epubs.siam.org/doi/abs/10.1137/S0097539798339430}
    Kaplan, Okasaki & Tarjan (2000)} (KOT), this data-structure
    implements the steque operations ({i i.e.} the deque operation
    except [eject]) and concatenation in {i amortised} constant time,
    using recursive slowdown and lazyness.

    A variant of this data structure using updates, analogous to
    {!Section3_4} is alluded to at the end of the section. No
    implementation of the variant is provided yet. *)

(** Markers for GADT: there is a bit of flexibility in the type of
    queues with an ill-formed kind of queue appearing temporarily during a
    {!pop} operation. These markers make it possible to ensure that
    well-formed queues are eventually produced. *)
type pseudo = PSEUDO
type wf = WELLFORMED

(** Prefixes are taken to be vectors of size at 2 to 6, which are seen
    as bounded-size deques. Note that because of bounded size, deque
    operations cannot always be performed, so each of the deque
    operations have a precondition, marked here by an [assert false]
    in the forbidden branches.

    Prefixes are defined as a GADT to allow temporary prefixes of size
    1 during {!pop}. *)
module Prefix = struct

  type (_,_) t =
    | One : 'a -> ('a,pseudo) t
    | Two : 'a * 'a -> ('a,'w) t
    | Three : 'a * 'a * 'a -> ('a,'w) t
    | Four : 'a * 'a * 'a * 'a -> ('a,'w) t
    | Five : 'a * 'a * 'a * 'a * 'a -> ('a,'w) t
    | Six : 'a * 'a * 'a * 'a * 'a * 'a -> ('a,'w) t

  let push : type a w. a -> (a,w) t -> (a,wf) t = fun x d ->
    match d with
    | One y -> Two (x,y)
    | Two (y,z) -> Three (x,y,z)
    | Three (y,z,w) -> Four (x,y,z,w)
    | Four (y,z,w,t) -> Five (x,y,z,w,t)
    | Five (y,z,w,t,s) -> Six (x,y,z,w,t,s)
    | Six _ -> assert false

  let pop : 'a. ('a,wf) t -> 'a * ('a,wf) t = function
    | Two _ -> assert false
    | Three (x,y,z) -> x , Two (y,z)
    | Four (x,y,z,w) -> x , Three(y,z,w)
    | Five (x,y,z,w,t) -> x , Four (y,z,w,t)
    | Six (x,y,z,w,t,s) -> x , Five (y,z,w,t,s)

  (** Total but may return prefixes of length 1. *)
  let naive_pop : 'a. ('a,wf) t -> 'a * ('a,pseudo) t = function
    | Two (x,y) -> x , One y
    | Three (x,y,z) -> x , Two (y,z)
    | Four (x,y,z,w) -> x , Three(y,z,w)
    | Five (x,y,z,w,t) -> x , Four (y,z,w,t)
    | Six (x,y,z,w,t,s) -> x , Five (y,z,w,t,s)

  let inject (d:(_,wf) t) s : (_,wf) t =
    match d with
    | Two (w,t) -> Three (w,t,s)
    | Three (z,w,t) -> Four (z,w,t,s)
    | Four (y,z,w,t) -> Five (y,z,w,t,s)
    | Five (x,y,z,w,t) -> Six (x,y,z,w,t,s)
    | Six _ -> assert false

end


(** Suffixes are taken to be vectors of size at 1 to 3, which are seen
    as bounded-size deques. Note that because of bounded size, deque
    operations cannot always be performed, so each of the deque
    operations have a precondition, marked here by an [assert false]
    in the forbidden branches. *)
module Suffix = struct

  type 'a t =
    | One of 'a
    | Two of 'a * 'a
    | Three of 'a * 'a * 'a

  let push x = function
    | One y -> Two (x,y)
    | Two (y,z) -> Three (x,y,z)
    | Three _ -> assert false

  let pop = function
    | One x -> assert false
    | Two (x,y) -> x , One y
    | Three (x,y,z) -> x , Two (y,z)

  let inject d z =
    match d with
    | One y -> Two (y,z)
    | Two (x,y) -> Three (x,y,z)
    | Three _ -> assert false

end

(** This catenable steque uses nested recursion, which is a
    significant step up in complexity with respect to
    {!Section3}. Nested recursion is central to fast concatenation of
    persistent list-like data structures.

    Note that contrary to {!Section3}. This representation ensures
    canonicity of the representation of the empty steque: since
    prefixes always have at least 2 elements, steques of the for
    [Q(p,c,s)] are non-empty.

    Like in {!Section3}, prefixes minimal and maximal capacity are
    called {i red} and the other are {i green}. Suffixes, on the other
    hand are red only if they are full ({i i.e.} they have three
    elements), since we won't be trying to pop from them. *)
type ('a,'w) t' =
  | Empty
  | S of 'a Suffix.t
  | Q of ('a,'w) Prefix.t * 'a u t Lazy.t * 'a Suffix.t
and 'a u =
  | P of ('a,wf) Prefix.t * 'a u t
and 'a t = ('a,wf) t'


(** {6 Push} *)

(** The [push] operation is fairly simple. Like in {!Section3}, the
    [gp] function which is supposed to turn the prefix green is
    inlined. When splitting a full prefix or suffix, there is a unique
    choice of splitting which produces no red prefix or suffix, taking
    this splitting determines the [push] process. *)

let rec push : type a w. a -> (a,w) t' -> a t = fun x d ->
  match d with
  | Q( Prefix.Six(y,z,w,t,s,r) , c , suf ) ->
      Q( Prefix.Four(x,y,z,w) ,
         lazy ( push (P (Prefix.Three(t,s,r), Empty)) (Lazy.force c) ) ,
         suf )
  | Q( pre , c , suf ) ->
      Q( Prefix.push x pre ,
         c ,
         suf )
  | S( Suffix.Three(y,z,w) ) ->
      Q ( Prefix.Three(x,y,z) ,
          Lazy.from_val Empty ,
          Suffix.One(w) )
  | S( suf ) ->
      S ( Suffix.push x suf )
  | Empty ->
      S ( Suffix.One x )

(** {6 Inject} *)

(** The [inject] operation is similar to [push]. Note that in one
    occurrence, when splitting a suffix, a red (size two) prefix is
    created. *)
let rec inject : 'a. 'a t -> 'a -> 'a t = fun d x ->
  match d with
  | Q( pre , c , Suffix.Three(y,z,w) ) ->
      Q ( pre ,
          lazy ( inject (Lazy.force c) (P (Prefix.Two(y,z),Empty)) ) ,
          Suffix.Two(w,x) )
  | Q( pre , c , suf ) ->
      Q ( pre ,
          c ,
          Suffix.inject suf x )
  | S( Suffix.Three(y,z,w) ) ->
      Q( Prefix.Three(y,z,w) ,
         Lazy.from_val Empty ,
         Suffix.One(x) )
  | S( suf ) ->
      S ( Suffix.inject suf x )
  | Empty ->
      S ( Suffix.One x )

(** {6 Catenate} *)

(** The [catenate] operation is {i not} recursive. So, it being
    constant (amortised) time depends solely on the analysis of
    {!push} and {!pop}. *)

type 'a merged =
  | Single of ('a,wf) Prefix.t
  | Double of ('a,wf) Prefix.t * ('a,wf) Prefix.t

(** Combines a suffix and a prefix into a single prefix of length at
    most 5 or two prefixes, the first one having length 4, and the
    second length 2 to 5. It is used to combine the suffix of the
    first queue with the prefix of the second queue for catenation. *)
let merge : type a w. a Suffix.t -> (a,w) Prefix.t -> a merged = fun suf pre ->
  match suf,pre with
  | Suffix.One(x), Prefix.One(y) -> Single (Prefix.Two(x,y))

  | Suffix.One x , Prefix.Two(y,z) -> Single (Prefix.Three(x,y,z))
  | Suffix.Two(x,y) , Prefix.One(z) -> Single (Prefix.Three(x,y,z))

  | Suffix.One x , Prefix.Three(y,z,w)
  | Suffix.Two(x,y) , Prefix.Two(z,w) -> Single (Prefix.Four(x,y,z,w))
  | Suffix.Three(x,y,z) , Prefix.One(w) -> Single (Prefix.Four(x,y,z,w))

  | Suffix.One x , Prefix.Four(y,z,w,s)
  | Suffix.Two (x,y) , Prefix.Three(z,w,s)
  | Suffix.Three (x,y,z) , Prefix.Two(w,s) -> Single (Prefix.Five(x,y,z,w,s))

  | Suffix.One x , Prefix.Five(y,z,w,s,t)
  | Suffix.Two (x,y) , Prefix.Four(z,w,s,t)
  | Suffix.Three (x,y,z) , Prefix.Three(w,s,t) ->
      Double (Prefix.Four(x,y,z,w),Prefix.Two(s,t))

  | Suffix.One x , Prefix.Six(y,z,w,s,t,r)
  | Suffix.Two (x,y) , Prefix.Five(z,w,s,t,r)
  | Suffix.Three (x,y,z) , Prefix.Four(w,s,t,r) ->
      Double (Prefix.Four(x,y,z,w),Prefix.Three(s,t,r))

  | Suffix.Two (x,y) , Prefix.Six(z,w,s,t,r,o)
  | Suffix.Three (x,y,z) , Prefix.Five(w,s,t,r,o) ->
      Double (Prefix.Four(x,y,z,w),Prefix.Four(s,t,r,o))

  | Suffix.Three (x,y,z) , Prefix.Six(w,s,t,r,o,p) ->
      Double (Prefix.Four(x,y,z,w),Prefix.Five(s,t,r,o,p))

(** [catenate_ne q1 q2] concatenates a non-empty queue [q1] with a
    queue [q2] which may have a prefix of length 1. It would be better
    to enforce by type that [q1] is non-empty, but the involved
    boilerplate would make reading this file unpleasant. *)
let catenate_ne : type a w. a t -> (a,w) t' -> a t = fun d1 d2 ->
  match d1,d2 with
  | Q(pre1,c1,suf1) , Q(pre2,c2,suf2) ->

      begin match merge suf1 pre2 with
      | Single pre' ->
          Q( pre1 ,
             lazy ( inject (Lazy.force c1) (P(pre' , Lazy.force c2)) ),
             suf2 )
      | Double(pre'1,pre'2) ->
          let c' = lazy (
            inject (inject (Lazy.force c1) (P(pre'1,Empty))) @@ P(pre'2, Lazy.force c2)
          )in
          Q (pre1 , c' , suf2 )
      end

  (** If [d1] or [d2] is only a suffix (hence finite), then
      constant time concatenation is done by repeated {!push} and {!inject}. *)
  | S( Suffix.One x ) , d2 ->
      push x d2
  | S( Suffix.Two (x,y) ) , d2 ->
      push x @@ push y d2
  | S( Suffix.Three (x,y,z) ) , d2 ->
      push x @@ push y @@ push z d2
  | d1 , S( Suffix.One x ) ->
      inject d1 x
  | d1 , S( Suffix.Two (x,y) ) ->
      inject (inject d1 x) y
  | d1 , S( Suffix.Three (x,y,z) ) ->
      inject (inject (inject d1 x ) y) z
  | Empty , d -> assert false
  | d , Empty -> d

let catenate d1 d2 =
  match d1 with
  | Empty -> d2
  | d1 -> catenate_ne d1 d2


(** {6 Pop} *)

(** {!pop} is a partial function (empty queues cannot be
    popped). Partiality is modeled with an exception. *)
exception CannotPop

(** Non-recursive [pop] operation which may return queues with a
    prefix of length 1. Assumes that the queue is non-empty. *)
let naive_pop : 'a. 'a t -> ('a * ('a,pseudo) t') = function
  | Q ( pre , c , suf ) ->
      let (x,pre') = Prefix.naive_pop pre in
      x , Q(pre',c,suf)
  | S ( Suffix.One x ) ->
      x , Empty
  | S ( suf ) ->
      let (x,suf') = Suffix.pop suf in
      x , S suf'
  | Empty ->
      assert false

let rec pop : 'a. 'a t -> ('a*'a t) = function
  | Q ( Prefix.Two (x,y) , lazy Empty , Suffix.Three(z,w,s) ) ->
      x , Q( Prefix.Three (y,z,w) , Lazy.from_val Empty , Suffix.One s )
  | Q ( Prefix.Two (x,y) , lazy Empty , suf ) ->
      x , S (Suffix.push y suf)
  | Q ( Prefix.Two (x,y) , lazy c , suf ) ->

      (** Main case *)

      let (P(pre',d'),c') = naive_pop c in
      begin match pre',d' with
      | (Prefix.Two(_,_) | Prefix.Three(_,_,_)) , Empty ->
          (** Since [d'] is empty is cannot serve as a first argument
              to [catenate_ne]. Since [c'] may have a prefix of length
              1, it cannot serve as a second argument of
              [catenate]. So we "rectify" [c'] by making a recursive
              call to [pop] instead of [naive_pop]. *)
          let (P(pre'',d''),c'') = pop c in
          x , Q ( Prefix.push y pre'' ,
                  Lazy.from_val ( catenate d'' c'' ),
                  suf )

      | (Prefix.Two(_,_) | Prefix.Three(_,_,_)) , _ ->
          x , Q ( Prefix.push y pre' ,
                  Lazy.from_val ( catenate_ne d' c' ),
                  suf )

      | _ ->
          let (z,pre'') = Prefix.pop pre'  in
          let (w,pre'') = Prefix.pop pre'' in
          x , Q( Prefix.Three (y,z,w) ,
                 Lazy.from_val ( push (P(pre'',d')) c' ) ,
                 suf )
      end

  | Q ( pre , c , suf ) ->
      let (x,pre') = Prefix.pop pre in
      x , Q ( pre' , c , suf )
  | Empty ->
      raise CannotPop
  | S ( Suffix.One x ) ->
      x , Empty
  | S ( suf ) ->
      let (x,suf') = Suffix.pop suf in
      x , S suf'
