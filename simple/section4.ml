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


(** Prefixes are taken to be vectors of size at 2 to 6, which are seen
    as bounded-size deques. Note that because of bounded size, deque
    operations cannot always be performed, so each of the deque
    operations have a precondition, marked here by an [assert false]
    in the forbidden branches. *)
module Prefix = struct

  type 'a t =
    | Two of 'a * 'a
    | Three of 'a * 'a * 'a
    | Four of 'a * 'a * 'a * 'a
    | Five of 'a * 'a * 'a * 'a * 'a
    | Six of 'a * 'a * 'a * 'a * 'a * 'a

  let push x = function
    | Two (y,z) -> Three (x,y,z)
    | Three (y,z,w) -> Four (x,y,z,w)
    | Four (y,z,w,t) -> Five (x,y,z,w,t)
    | Five (y,z,w,t,s) -> Six (x,y,z,w,t,s)
    | Six _ -> assert false

  let pop = function
    | Two _ -> assert false
    | Three (x,y,z) -> x , Two (y,z)
    | Four (x,y,z,w) -> x , Three(y,z,w)
    | Five (x,y,z,w,t) -> x , Four (y,z,w,t)
    | Six (x,y,z,w,t,s) -> x , Five (y,z,w,t,s)

  let inject d s =
    match d with
    | Two (w,t) -> Three (w,t,s)
    | Three (z,w,t) -> Four (z,w,t,s)
    | Four (y,z,w,t) -> Five (y,z,w,t,s)
    | Five (x,y,z,w,t) -> Six (x,y,z,w,t,s)
    | Six _ -> assert false

  let eject = function
    | Two _ -> assert false
    | Three (w,t,s) -> Two (w,t) , s
    | Four (z,w,t,s) -> Three (z,w,t) , s
    | Five (y,z,w,t,s) -> Four (y,z,w,t) , s
    | Six (x,y,z,w,t,s) -> Five (x,y,z,w,t) , s

end


(** Prefixes are taken to be vectors of size at most 3, which are seen
    as bounded-size deques. Note that because of bounded size, deque
    operations cannot always be performed, so each of the deque
    operations have a precondition, marked here by an [assert false]
    in the forbidden branches. *)
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
type 'a t =
  | S of 'a Suffix.t
  | Q of 'a Prefix.t * 'a u t Lazy.t * 'a Suffix.t
and 'a u =
  | P of 'a Prefix.t * 'a u t

let empty = S Suffix.Zero

(** {6 Push} *)

(** The [push] operation is fairly simple. Like in {!Section3}, the
    [gp] function which is supposed to turn the prefix green is
    inlined. When splitting a full prefix or suffix, there is a unique
    choice of splitting which produces no red prefix or suffix, taking
    this splitting determines the [push] process. *)

(** The type annotation on the [push] function is necessary because
    the recursion is non-uniform: the recursive call to [push] is on a
    deque of type [('a*'a) t]. *)
let rec push : 'a. 'a -> 'a t -> 'a t = fun x d ->
  match d with
  | Q( Prefix.Six(y,z,w,t,s,r) , c , suf ) ->
      Q( Prefix.Four(x,y,z,w) ,
         lazy ( push (P (Prefix.Three(t,s,r), empty)) (Lazy.force c) ) ,
         suf )
  | Q( pre , c , suf ) ->
      Q( Prefix.push x pre ,
         c ,
         suf )
  | S( Suffix.Three(y,z,w) ) ->
      Q ( Prefix.Three(x,y,z) ,
          Lazy.from_val empty ,
          Suffix.One(w) )
  | S( suf ) ->
      S ( Suffix.push x suf )

(** {6 Inject} *)

(** The [inject] operation is similar to [push]. Note that in one
    occurrence, when splitting a suffix, a red (size two) prefix is
    created. *)
let rec inject : 'a. 'a t -> 'a -> 'a t = fun d x ->
  match d with
  | Q( pre , c , Suffix.Three(y,z,w) ) ->
      Q ( pre ,
          lazy ( inject (Lazy.force c) (P (Prefix.Two(y,z),empty)) ) ,
          Suffix.Two(w,x) )
  | Q( pre , c , suf ) ->
      Q ( pre ,
          c ,
          Suffix.inject suf x )
  | S( Suffix.Three(y,z,w) ) ->
      Q( Prefix.Three(y,z,w) ,
         Lazy.from_val empty ,
         Suffix.One(x) )
  | S( suf ) ->
      S ( Suffix.inject suf x )

(** {6 Catenate} *)

(** The [catenate] operation is {i not} recursive. So, it being
    constant (amortised) time depends solely on the analysis of
    {!push} and {!pop}. *)

type 'a merged =
  | Single of 'a Prefix.t
  | Double of 'a Prefix.t * 'a Prefix.t

(** Combines a suffix and a prefix into a single prefix of length at
    most 5 or two prefixes, the first one having length 4, and the
    second length 2 to 5. It is used to combine the suffix of the
    first queue with the prefix of the second queue for catenation. *)
let merge suf pre =
  match suf,pre with
  | Suffix.Zero, Prefix.Two(x,y) -> Single (Prefix.Two(x,y))

  | Suffix.Zero , Prefix.Three(x,y,z)
  | Suffix.One x , Prefix.Two(y,z) -> Single (Prefix.Three(x,y,z))

  | Suffix.Zero , Prefix.Four(x,y,z,w)
  | Suffix.One x , Prefix.Three(y,z,w)
  | Suffix.Two(x,y) , Prefix.Two(z,w) -> Single (Prefix.Four(x,y,z,w))

  | Suffix.Zero , Prefix.Five(x,y,z,w,s)
  | Suffix.One x , Prefix.Four(y,z,w,s)
  | Suffix.Two (x,y) , Prefix.Three(z,w,s)
  | Suffix.Three (x,y,z) , Prefix.Two(w,s) -> Single (Prefix.Five(x,y,z,w,s))

  | Suffix.Zero , Prefix.Six(x,y,z,w,s,t)
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

let catenate d1 d2 =
  match d1,d2 with
  | Q(pre1,c1,suf1) , Q(pre2,c2,suf2) ->

      begin match merge suf1 pre2 with
      | Single pre' ->
          Q( pre1 ,
             lazy ( inject (Lazy.force c1) (P(pre' , Lazy.force c2)) ),
             suf2 )
      | Double(pre'1,pre'2) ->
          let c' = lazy (
            inject (inject (Lazy.force c1) (P(pre'1,empty))) @@ P(pre'2, Lazy.force c2)
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
  | S Suffix.Zero , d | d , S Suffix.Zero -> d


(** {6 Pop} *)

(** {!pop} is a partial function (empty queues cannot be
    popped). Partiality is modeled with an exception. *)
exception CannotPop

let rec pop : 'a. 'a t -> ('a*'a t) = function
  | Q ( Prefix.Two (x,y) , lazy (S Suffix.Zero) , Suffix.Three(z,w,s) ) ->
      x , Q( Prefix.Three (y,z,w) , Lazy.from_val empty , Suffix.One s )
  | Q ( Prefix.Two (x,y) , lazy (S Suffix.Zero) , suf ) ->
      x , S (Suffix.push y suf)
  | Q ( Prefix.Two (x,y) , lazy c , suf ) ->

      (** Main case *)

      (** This recursive call to [pop] is not quite correct as the
          implementation of KOT mandates that in some cases, a
          non-recursive version of [pop] be called (it may create a size
          one prefix). *)
      let (P(pre',d'),c') = pop c in
      begin match pre' with
      | Prefix.Two(_,_) | Prefix.Three(_,_,_) ->
          x , Q ( Prefix.push y pre' ,
                  Lazy.from_val ( catenate d' c' ),
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
  | S ( Suffix.Zero ) ->
      raise CannotPop
  | S ( suf ) ->
      let (x,suf') = Suffix.pop suf in
      x , S suf'
