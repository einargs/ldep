# TODO
* Implement typecheck
* Write down what the type theory is
* Refactor the `total_ordering` stuff out of `Core.Name` and
  into something like `Util.TotalOrdering`. Define a typeclass
  that indicates that there is a total ordering on a type and
  define variants of `ordmap` and `ordset` that just take a key
  type (that has to have an instance of the typeclass) and a
  value type.
* Implement elaboration monad
  1. Develop list of elaboration monad tactics
  2. Implement skeleton of the elaboration monad
  3. Implement elaboration monad tactics (add each tactic below)
