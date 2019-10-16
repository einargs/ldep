module Core.Weaken

open Core.Name

class weaken tm = {
  weaken_ns' : vars:list local_name -> ns:list local_name -> tm vars -> Tot (tm (ns @ vars))
}

let weaken_ns
  (#vars:list local_name)
  (tm:list local_name -> Type)
  [|d:weaken tm|]
  (ns:list local_name)
  (t:tm vars)
  = weaken_ns' #tm vars ns t

let weaken'
  (#vars:list local_name)
  (#name:local_name)
  (tm:list local_name -> Type)
  [|d:weaken tm|]
  (t:tm vars)
  : tm (name :: vars)
  = weaken_ns' #tm vars [name] t
