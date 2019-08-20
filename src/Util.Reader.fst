module Util.Reader

(** Internal represenstation of the reader monad. *)
private let reader (r:Type) (a:Type) = r -> M a

(** Convert a function to the reader monad. *)
private val to_reader : #r:Type -> #a:Type -> (r -> M a) -> reader r a
let to_reader #r #a f = f

(** Lift a value into the reader monad. *)
private val return_reader : r:Type -> a:Type -> a -> reader r a
let return_reader r a x = fun env -> x

(** Bind a function in the reader monad. *)
private val bind_reader
  : r:Type -> a:Type -> b:Type
  -> x:reader r a -> f:(a -> reader r b) -> reader r b
let bind_reader _ _ _ x f =
  fun env ->
    let z = x env in
    f z env

(** Implementation of the `get` action in the reader monad. *)
private val reader_get : r:Type -> unit -> reader r r
let reader_get _ () = to_reader (fun env -> env)

(** Define the READER effect for the reader monad *)
total reifiable reflectable new_effect {
  READER (r:Type0) : a:Type -> Effect
  with repr   = reader r
     ; bind   = bind_reader r
     ; return = return_reader r
     ; get    = reader_get r
}
