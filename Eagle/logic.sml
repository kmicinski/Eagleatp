(* Logic representation for Eagle
 * Kristopher Micinski, 2007.
 *)

(* General logic definitions *)
datatype 'a formula = Formula of 'a;

datatype 'a result = Theorem of 'a | Conjecture of 'a;

datatype 'a axiom = Axiom of 'a;

datatype 'a proof = Proof of 'a;

type 'a infrule = 'a list -> 'a;

signature LOGICSYNTAX =
  sig
  (* The datatype of formulas in the logic *)
  type formula;
  (* A utility function to turn a formula into a string *)
  val tostring : formula -> string
  end;

type 'a parser = string -> 'a;

signature INFRULES =
  sig
  type rule;
  eqtype ruleid; (* A way to identify a rule *)
  val ruletab : (rule, ruleid) table; (* A table of rules *)
  end;

signature LOGIC =
  sig
  structure Syntax : LOGICSYNTAX; (* The syntax to be used with this logic,
				   * including the type of the formula and
				   * how it is represented. *)
  val parsewff : Syntax.formula parser; (* A parser which converts strings
					 * to the type of formula for the logic *)
  type normalform; (* A convinent way to represent formulas
		    * in this specific logic, this could be
		    * CNF, regular formula, sequent form, etc...
		    *)
  
  (* Convert a formula in the syntax to the normal form for the logic,
   * for example, convert a formula to a sequent *)
  val converttonormal : Syntax.formula -> normalform;
  
  val parsenormal : normalform parser; (* Parse a string in the normal form into
					* the normal form of the logic *)
  
  type proof; (* The representation of a proof in the logic *)
  
  val proofstr : proof -> string; (* A function to transform a proof into a string *)

  structure InfRules : INFRULES; (* An implementation of inference rules *)
  
  type inference; (* The type of inferences in this logic *)
  
  (* Apply an inference rule in the logic.
   * I hope that this function is general enough to be used
   * in many logics. The first argument should be the structure
   * to which the rule is applied. The second should be the identifier
   * of the inference rule. Some rules require extra arguments
   * (A pretty simple good example of this is the or-introduction
   * rule in sequent calculi). So extra arguments for the specific
   * rules in the logic can be conveyed in the third argument.
   *)
  val 'a applyrule : (ruleargument * InfRules.ruleid * 'a option) -> inference;
  
  type proofargument; (* The type of data which can be given to a proof function *)

  (* Attempt to prove a formula in the logic. 
   * This could result in a proof, or could result
   * in a failed proof attempt. For this reason, I have included
   * an option for the optional proof, and a result which
   * will be either a theorem of a conjecture. This brings
   * about the question, "A theorem of what type?," which
   * I am currently (August, 2007) with normalform
   *)
  val prove : proofargument -> (proof option * normalform result);
  
  end;
  
(* An exception which is thrown when a target is given
 * the wrong type of formula *)
exception Formula_Type;

(* representation of first order logic *)
structure FOLSyntax =
  struct

  type variable = string;
  
  type constant = string;

  datatype formula = All of variable * formula
		   | Exists of variable * formula
		   | Negation of formula
		   | Implies of formula * formula
		   | Conj of formula * formula
		   | Disj of formula * formula
		   | Predicate of string * formula list
	           | Function of string * formula list
		   | Variable of string
		   | Constant of string;
 
  fun commaize ([l]) = l
    | commaize (l::r) = l ^ ", " ^ commaize r
    | commaize (_) = "";

  fun parenthesize string = "(" ^ string ^ ")";

  fun addparenthesis(string, Negation(Predicate(_))) = string
    | addparenthesis(string, Negation(_)) = parenthesize string
    | addparenthesis(string, Predicate(x,formulas)) = string
    | addparenthesis(string, _) = parenthesize string;
  
  fun tostring (All(x,rest)) = "@" ^ x ^ " " ^ tostring(rest)
    | tostring (Exists(x,rest)) = "!" ^ x ^ " " ^ tostring(rest)
    | tostring (Negation(rest)) = "~" ^ (addparenthesis (tostring(rest), Negation(rest)))
    | tostring (Implies(a,b)) = (addparenthesis(tostring(a), a)) ^ " => " ^ (addparenthesis(tostring(b), b))
    | tostring (Conj(a,b)) = addparenthesis(tostring(a),a) ^ " & " ^ (addparenthesis(tostring(b), b))
    | tostring (Disj(a,b)) = addparenthesis(tostring(a),a) ^ " | " ^ (addparenthesis(tostring(b), b))
    | tostring (Predicate(s,formulas)) = s ^ "(" ^ commaize(List.map(fn x => tostring x) formulas) ^ ")"
    | tostring (Function(s,formulas)) = s ^ "(" ^ commaize(List.map(fn x => tostring x) formulas) ^ ")"
    | tostring (Variable(s)) = s
    | tostring (Constant(s)) = s;
  
  fun resultstr (Theorem(f:formula)) = "|- " ^ (tostring f)
  | resultstr (Conjecture(f:formula)) = "? " ^ (tostring f);
  
  end;

(*

open FOL;

val foltestf = All("x",Implies(Predicate("P", []), Negation(Predicate("Y", [Variable "x"]))));

*)

(* representation of propositional logic *)
structure PropLSyntax =
  struct
  
  type propname = string;

  datatype boolval = True | False;
  
  datatype formula = Negation of formula
		       | Equivalence of formula * formula
		       | Equals of formula * formula
		       | Implies of formula * formula
		       | Conj of formula * formula
		       | Disj of formula * formula
		       | Proposition of propname
		       | BoolVal of boolval;
  
  fun tostring (Negation(x)) = "~(" ^ tostring x ^ ")"
    | tostring (Equivalence(a, b)) = tostring a ^ " == " ^ tostring b
    | tostring (Equals(a,b)) = tostring a ^ " = " ^ tostring b
    | tostring (Implies(a,b)) = tostring a ^ " => " ^ tostring b
    | tostring (Conj(a,b)) = tostring a ^ " & " ^ tostring b
    | tostring (Disj(a,b)) = tostring a ^ " | " ^ tostring b
    | tostring (Proposition(b)) = b ^ "()"
    | tostring (BoolVal(True)) = "T"
    | tostring (BoolVal(False)) = "F";

  fun resultstr (Theorem(f:formula)) = "|- " ^ (tostring f)
  | resultstr (Conjecture(f:formula)) = "? " ^ (tostring f);
  
  end;
