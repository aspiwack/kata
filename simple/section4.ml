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
    [Q(p,c,s)] are non-empty. *)
type 'a t =
  | S of 'a Suffix.t
  | Q of 'a Prefix.t * ('a Prefix.t * 'a t) t Lazy.t * 'a Suffix.t
