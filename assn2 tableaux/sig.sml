signature PropLogicTableau =
sig
exception Atom_exception
datatype Prop =
ATOM of string |
NOT of Prop |
AND of Prop * Prop |
OR of Prop * Prop |
COND of Prop * Prop |
BIC of Prop * Prop
type Argument = Prop list * Prop
val tableau: Prop list -> unit
end;