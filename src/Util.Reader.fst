module Util.Reader

private let reader (r:Type) (a:Type) = r -> M a

private val to_reader : #r:Type -> #a:Type -> (r -> M a) -> reader r a
let to_reader #r #a f = f

private val return_reader : r:Type -> a:Type -> a -> reader r a
let return_reader r a x = fun env -> x

private val bind_reader
  : r:Type -> a:Type -> b:Type
  -> x:reader r a -> f:(a -> reader r b) -> reader r b
let bind_reader _ _ _ x f =
  fun env ->
    let z = x env in
    f z env

private val reader_get : r:Type -> unit -> reader r r
let reader_get _ () = to_reader (fun env -> env)

total reifiable reflectable new_effect {
  READER (r:Type0) : a:Type -> Effect
  with repr   = reader r
     ; bind   = bind_reader r
     ; return = return_reader r
     ; get    = reader_get r
}
