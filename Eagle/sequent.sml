(* Assistant functions and types to assist in building sequent
 * based logics.
 * By Kristopher Micinski,
 * For the Eagle Logic System / ATP
 *)

datatype 'a sequent = Sequent of 'a list * 'a;

(*
signature SEQUENTCALC =
  sig
      type rule
      val rules : rule list
      val 'a applyrule : (string * 'a rule * premises) -> 'a
      val 'a rulestr : 'a rule -> string
  end;
*)

fun prm (Sequent (prms, con), n) = List.nth (prms, n-1);

fun conclusion (Sequent (prms, con)) = con;

(* A parser for sequent calculi
 * A high order function for parsing sequent calculi
 * This is kind of lazy, lots of people use commas for connectives,
 * if we split that with our scanner, you get all the commas in the
 * things like predicates and kruft. So here this is a high order
 * function for parsing sequents, that typically look something like:
 * "P ^ Q ^ M |- P & M"
 * like I said, were lazy, and we'll use ^ for connecting premesis
 * for now. So you give this function a tuple of the turnstile symbol
 * you want to use (typically "|-") and the connective you want to use
 * for premises (probably "^") the only requirement for this to work
 * is that the two symbols must be things different than special characters
 * for the parser that parses the formulas. The result of this function
 * should be a tuple of ('a list * 'a) which is meant to imply,
 * the premises and the conclusion.
 *)

fun parsesequent (turns:string, prmscon:string) (parseformula:'a parser) (input:string) =
  let
      val (prmlst, conclusion) = (scanner [turns] Char.isSpace) input;
      val prms = (scanner [prmscon] Char.isSpace) prmlst;
      fun convertprms (hd::tl) = (parseformula hd)::(convertprms tl)
	| convertprms (nil) = nil;
  in
      ((convertprms prms), parseformula conclusion)
  end;
