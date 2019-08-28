module Util.Result

type result (b:Type) (a:Type) =
  | Err : err:b -> result b a
  | Ok : value:a -> result b a

val bind_result : result 's 'a -> f:('a -> result 's 'b) -> result 's 'b
let bind_result r f =
  match r with
  | Ok v -> f v
  | Err err -> Err err
