module type S = sig
  type t;;
  val v : t;;
  val f : t -> t;;
end;;

module F (X : S) (Y : S) = struct
  let w = Y.f X.v;;
end;;

module Bool = struct
  type t = bool;;
  let v = false;;
  let f b = true;;
end;;

module Int = struct
  type t = int;;
  let v = 30;;
  let f x = x + 1;;
end;;

module M : sig val w : int end = F Bool Int;;

module F (X : sig end) : sig type t end = struct type t = int;; end;;

module M = F struct end;;
module N = F struct end;;
#show M.t;;
#show N.t;;