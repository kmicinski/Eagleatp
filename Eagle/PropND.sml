(* An implementation of Propositional Natural Deduction logic
 * for the Eagle Logic System / ATP
 * By Kristopher Micinski
 * August 2007
 *)

(* Inference rules for Propositional natural deduction.
 * This system is based on the propositional natural deduction
 * given in Chapter 6. of Gries and Schneider's
 * 'A Logical Approach to discrete math'
 * Now, these are just simple rule implementations, they are
 * not really useful, and they don't do pattern matching that
 * allows a large flexibility in the proof construction.
 * To be really effective I plan to use these rules along with
 * an application procedure, such as renaming, or a simple
 * pattern matcher for the logic syntax. But for now these
 * are just the base inference rules of the logic. I think
 * that many of the following logics should be constructed
 * in this way, with the rules implemented as simple procedures,
 * and their application seperate from the rules themselvs.
 *
 * I am currently working on generalizing the concept of a logic
 * in cryter, which also requires a signature on inference
 * rules. I hope to get this to be general enough so we can
 * implement many logis cleanly, but also specific enough
 * so that we don't have to have way too many types. I
 * think it might be a bit bloated now, if you have any
 * ideas, please feel free to teel.
 * --Kris Micinski, Aug 28, 2007
 *)
structure PropNDRules =
  struct
  local
      open PropLSyntax
  in
  eqtype ruleid = string;
  
  datatype ruleargument = Sequentarg of formula sequent
			| Formulaarg of formula list
  
  datatype ruleoption = NoOption
		      | FormulaOpt of formula
  
  (* The type of a rule is currently the tuple of its name and function
   * I also plan to add another element to describe what the rule does.
   * For example, in formula notation, which can be printed to describe
   * the rule to the user.
   *
   * Hrrm, the rule table indexes the rules by their names, but we
   * still keep the rule name in the rule type. I'm not sure if this
   * should be viewed as redundancy...
   * Kris -- Aug 28 2007
   *)
  type rule = (string * ((ruleargument * ruleoption) -> formula))
  
  fun ConjIntro (Formulaarg([a,b]), NoOption) = Conj(a, b) | ConjIntro (_, _) = raise PremiseExn
  
  and DisjIntroL (Formulaarg([a]),FormulaOpt(b))) = Disj(b, a) | DisjIntroL (_, _) = raise PremiseExn
  
  and DisjIntroR (Formulaarg([a]),FormulaOpt(b)) = Disj(a, b) | DisjIntroR (_, _) = raise PremiseExn
  
  and ImpIntro (Sequentarg(Sequent(premises, conclusion))) =
      let
	  fun makeands ([t]: formula list) = t
	    | makeands (h::t) = Conj(h, makeands t)
	    | makeands (nil) = nil (* Originally I had this as BoolVal True, but I think nil captures
				    * the standard implementation of natural deduction. --Kris Micinski, Aug 28 *)
      in
	  Implies(makeands premises, conclusion)
      end
  
  and EquivIntro (Formulaarg([Implies(a,b), Implies(c,d)]), NoOption) = if (a = d andalso b = c) then Equivalence (a, b)
									   else raise PremiseExn
    | EquivIntro (_, _) = raise PremiseExn
  
  and NotIntro (Sequentarg(Sequent([premise], Conj(Negation(a), b))), NoOption) =
      if a = b then (Negation premise) else raise PremiseExn
    | NotIntro (Sequentarg(Sequent([premise], Conj(a, Negation(b)))), NoOption) =
      if a = b then Negation premise else raise PremiseExn
    | NotIntro (_, _) = raise PremiseExn
  
  and TrueIntro (Formulaarg([Equivalence(a, b)]), NoOption) = if a = b then BoolVal True else raise PremiseExn
  | TrueIntro (_, _) = raise PremiseExn
  
  and FalseIntro (Formulaarg([Negation (BoolVal True)]), NoOption) = BoolVal False
  | FalseIntro (_, _) = raise PremiseExn
  
  and ConjElimR (Formulaarg([Conj(a, b)]), NoOption) = a
  | ConjElimR (_, _) = raise PremiseExn
  
  and ConjElimL (Formulaarg([Conj(a, b)]), NoOption) = b
  | ConjElimL (_, _) = raise PremiseExn
  
  and DisjElim (Formulaarg([Disj(a, b), Implies(c, d), Implies(e, f)]), NoOption) =
      if (a = c andalso b = e andalso d = f) then d else raise PremiseExn
  | DisjElim (_, _) = raise PremiseExn
  
  and ImpElim (Formulaarg([p:formula, Implies(a, q)]), NoOption) = if p = a then q else raise PremiseExn
  | ImpElim (_, _) = raise PremiseExn
  
  and EquivElimL (Formulaarg([Equivalence(a, b)]), NoOption) = Implies(a, b)
  | EquivElimL (_, _) = raise PremiseExn
  
  and EquivElimR (Formulaarg([Equivalence(a, b)]), NoOption) = Implies(b, a)
  | EquivElimR (_, _) = raise PremiseExn
  
  and NotElim (Sequentarg(Sequent([Negation(p)], Conj(a, Negation(b)))), NoOption) = if a = b then p else raise PremiseExn
  | NotElim (_, _) = raise PremiseExn
  
  and TrueElim (Formulaarg([BoolVal (True)]), Formulaoption(a)) = Equivalence(a, a)
  | TrueElim (_, _) = raise PremiseExn
  
  and FalseElim (Formulaarg([Negation (BoolVal (False))]), NoOption) = BoolVal (True)
  | FalseElim (_, _) = raise PremiseExn
  
  (* The table for storing all of the rules *)
  val ruletab = (("ConjIntro", ConjIntro), "ConjIntro")
		tabcons (("DisjIntroL", DisjIntroL), "DisjIntroL")
		tabcons (("DisjIntroR", DisjIntroR), "DisjIntroR")
		tabcons (("ImpIntro", ImpIntro), "ImpIntro")
		tabcons (("EquivIntro", EquivIntro), "EquivIntro")
		tabcons (("NotIntro", NotIntro), "NotIntro")
		tabcons (("TrueIntro", TrueIntro), "TrueIntro")
		tabcons (("FalseIntro", FalseIntro), "FalseIntro")
		tabcons (("ConjElimR", ConjElimR), "ConjElimR")
		tabcons (("ConjElimL", ConjElimL), "ConjElimL")
		tabcons (("DisjElim", DisjElim), "DisjElim")
		tabcons (("ImpElim", ImpElim), "ImpElim")
		tabcons (("EquivElimL", EquivElimL), "EquivElimL")
		tabcons (("EquivElimR", EquivElimR), "EquivElimR")
		tabcons (("NotElim", NotElim), "NotElim")
		tabcons (("TrueElim", TrueElim), "TrueElim")
		tabcons (("FalseElim", FalseElim), "FalseElim")
		tabcons Table.niltable;
  
  end
  end;

(* Propositional Natural Deduction, this is a simple proof system for
 * propositional logic based on sequents.
 * Often proofs are done like this:
 * P & A |- A & P
 * 1: P (Premise 1)
 * 2: A (Premise 2)
 * 3: A & P (&-Intro: 1, 2)
 * Each step in the proof is a formula and a justification. A proof in
 * this logic is a list of proof steps, where the last step should be
 * the conclusion of the initial sequent. Therefore, a proof is a list
 * of steps which attains the goal, and a sequent which the list
 * proves. The sequent is taken to be a theorem, and the goal is to
 * be solved.
 * -- Kris Micinski, Aug 30, 2007
 *)
structure PropNDLogic =
  struct
  structure Syntax = PropLSyntax;
  
  val parsewff = PropLParser.parsewff;
  
  type normalform = 
  
  (* Convert a formula from propositional logic into sequent form,
   * we just make a formula a sequent with no premises *)
  fun converttonormal (formula:PropLSyntax.formula) = Sequent (nil, formula);
  
  fun parsenormal (sequent:string) =
    let
	val (prms, con) = parsesequent normalseqtup parsewff;
    in
	Sequent (prms, con)
    end;
  
  datatype inference = Premise of PropLSyntax.formula
		     | Inference of PropLSyntax.formula * inference * InfRules.ruleid;
  
  
  end;

structure PropNDCalc =
  struct
  local
      open PropLSyntax
  in
  
  (* The type of a rule for Propositional logic
   *     [formula list]
   *     --------------
   *        formula
   * is the format, a string describes the name
   * of the rule.
   *)
  type rule = (formula list * formula * string);
  val rules = [ ([Negation (BoolVal (False))], BoolVal (True), "~-Elimination") ]
  
  fun applyrule (name, premises) =
      let
	  tab = sdfsd
	  
  end
  end;
*)
