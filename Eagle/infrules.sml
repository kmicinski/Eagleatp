(* Some simple definitions to assist in writing
 * inference rules for logics.
 * By Kristopher Micinski
 * For the Eagle Logic System / ATP
 *)

(* For example, formula list -> formula *)
type 'a infrule = 'a list -> 'a;

(* An exception to indicate that incorrect
 * premisis were given to the inference rule *)
exception PremiseExn;

(* A structure to be used in logics which have no inference rules
 * The only good example I can find of this right now is the truth
 * Table logic for Propositional sentences. When you're valuating
 * sentences in Propositional Logic, it makes no sense to use
 * inference rules.
 *)
structure NoInferences : INFRULES =
  struct
  type rule = unit;
  eqtype ruleid = unit;
  val ruletab = Table.niltable;
  fun applyrule 
