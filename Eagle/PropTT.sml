(* Propositional Truth Table proof implementation
 * By Kristopher Micinski
 * For the Eagle Logic System / ATP
 * This is a fairly simple proof method for
 * propositional logic which creates truth tables
 * for propositional sentences.
 *)

structure PropTT : LOGIC =
  struct
  local
      open PropLSyntax;
  in
  structure Syntax = PropLSyntax;
  val parsewff = PropLParser.parsewff;
  
  (* A list of proposition names and their values, and the value
   * of the whole formula. *)
  type valuation = (propname * bool) list * bool;
  
  (* Our normal form is just the same Propositional Logic *)
  type normalform = PropLSyntax.formula;
  
  val converttonormal = (fn x => x);
  
  val parsenormal = PropLParser.parsewff;
  
  structure InfRules = NoInferences; (* There are no inference rules for
				      * This proof method *)
  
  type inference = ();
  
  type ruleargument = ();
  
  val applyrule (arg, id, option) = ();
  
  (* A list of all the possible valuations of the formulas *)
  type proof = valuation list;
  
  type proofargument = formula;
  
  fun prove (sentence:proofargument) =
    let
	val propositionnames = extractpropnames sentence;
	val proofattempt = enumvaluations (sentence, propositionnames);
    in
	if checkvaluations proofattempt then
	    ((Theorem sentence, proofattempt) : (formula result * ttproof))
	    else (Conjecture sentence, proofattempt)
    end
  and
  checkvaluations ((individualvals, true)::t) = checkvaluations t
  | checkvaluations ((individualvals, false)::t) = false
  | checkvaluations (nil) = true
  and
  enumvaluations (sentence:formula, propnames) =
    let
	val valuemap = enumvallist propnames;
	fun producevals (h::r) =
	    (h, decide (sentence, h)) :: (producevals r)
	  | producevals (_) = nil
    in
	producevals valuemap
    end
  and
  decide (Negation(f), valmap) = not (decide (f, valmap))
  | decide (Equivalence(a, b), valmap) = if (decide (a, valmap) = decide (b, valmap)) then true else false
  | decide (Equals(a, b), valmap) = if (decide (a, valmap) = decide (b, valmap)) then true else false
  | decide (Implies(a, b), valmap) = if (decide (a, valmap) = decide (b, valmap)) then true else false
  | decide (Conj(a, b), valmap) = if (decide (a, valmap) = true andalso decide (b, valmap) = true)
				     then true else false
  | decide (Disj(a, b), valmap) = if (decide (a, valmap) = true orelse decide (b, valmap) = true)
				     then true else false
  | decide (BoolVal(True), valmap) = true
  | decide (BoolVal(False), valmap) = false
  | decide (Proposition(n), valmap) = lookupprop (n, valmap)
  and
  lookupprop (n:string, (name, value)::t) = if (n = name) then value else lookupprop (n, t)
  | lookupprop (n, nil) = false (* This should never happen *)
  and
  (* This is cute *)
  enumvallist ([h]) =
      [[(h, true)], [(h, false)]]
  | enumvallist (h::r) =
    let
	val initiallist = enumvallist r
    in
      (List.map (fn x => (h, true)::x) initiallist) @ (List.map (fn x => (h, false)::x) initiallist)
    end
  | enumvallist (nil) = []
  and
  extractpropnames (f:formula) =
    let
	fun assemblenamelist (Negation(f)) = assemblenamelist f
	  | assemblenamelist (Equivalence(a,b)) = (assemblenamelist a) @ (assemblenamelist b)
	  | assemblenamelist (Equals(a,b)) = (assemblenamelist a) @ (assemblenamelist b)
	  | assemblenamelist (Implies(a,b)) = (assemblenamelist a) @ (assemblenamelist b)
	  | assemblenamelist (Conj(a,b)) = (assemblenamelist a) @ (assemblenamelist b)
	  | assemblenamelist (Disj(a,b)) = (assemblenamelist a) @ (assemblenamelist b)
	  | assemblenamelist (Proposition(n)) = [n]
	  | assemblenamelist (_) = []
	and removeduplicates (h::t, lst) =
	    if (List.exists (fn x => x = h) lst) then
		removeduplicates (t, lst)
	    else removeduplicates (t, h::lst)
	  | removeduplicates (_, lst) = List.rev lst;
    in
	removeduplicates (assemblenamelist f, nil)
    end;
  
  end
  end;
