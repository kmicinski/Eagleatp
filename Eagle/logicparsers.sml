(* Parsers for logics - Eagle
 * These are simple parsers for the logics currently implemented
 * with the Eagle logic system. Later parser combinators may
 * be used, but I'm not a functional programmer by birth.
 * Kristopher Micinski - 2007
 * What do you know, I'm not a functional programmer, but
 * I'm pretty sure taking the time to read about parsing combinators
 * and using them instead would have been easier than the wierd
 * kind of thing I've got going on here. *hrrm* Anyway, I'm sure
 * it'll either be considered elegant or rewritten...
 * Kris Micinski - Aug 16 
 * Okay, I've finished the parsers for FOL and Prop. Logic
 * Kris micinski - Aug 23
 *)

(* Explanation of the grammar used here:
 * For all of the following parsers constructed for Eagle
 * The comment procedding them should describe the type of
 * grammar which is implemented by each parser.
 * 
 * <X> - Exactly one
 * [X] - Zero or one
 * | - Exclusive or
 * (X) - Zero or more
 * [string] - a string
 * other notes as needed...
 *
 * Juxtaposition implies conjunction, for example:
 * [string] "&" [string]
 * matches "Pan&Yet"
 *)

exception Parser_Exn of string list * string;

(* scanner - Create a simple scanner.
 * (string list) -> (char -> bool) -> string -> string list
 * Makes a simple scanner function, usually called with something like:
 * val scan = scanner seperators whitespace
 * scan string
 * The first argument is for the list of seperator strings,
 * the second argument is for stripping out whitespace.
 * 
 * Well, this started out as a small function, but it grew in a couple
 * of hours to a pretty useful functional tokenizer -- I hope it works :)
 * -- Kris Micinski -- Aug 19???
 *)
fun scanner (seperatorlist:string list) (iswhitespace: char -> bool) (string:string) =
  let
      val cutwhite = List.map (fn a => (implode (List.filter (fn x => not (iswhitespace x)) (explode a))));
      fun splitstr ("", tokens) =
	  tokens
	| splitstr (str, tokens) =
	  let
	      val (lentoprefix,s) = calclentoprefix (seperatorlist, str)
	  in
	      case lentoprefix of
		  0 => splitstr ((strdrop (str, s)), tokens @ [(strtake (str, s))])
		| n => splitstr ((strdrop (str, n)), tokens @ [(strtake (str, n))])
	  end
      (* Try to match this current section of string against all prefixes given;
       * if one is found, return (0, size of matched prefix), 0 to indicate no length
       * to prefix. On the other hand, if no matches are made, use the findprefix function
       * to find the length to the closest prefix, this is a computationally hard problem. *)
      and calclentoprefix (a::b, str) =
	  if (String.isPrefix a str)
	     then (0, String.size a)
	     else calclentoprefix (b, str)
	| calclentoprefix ([], str) =
	  (findprefix (seperatorlist, strdrop (str, 1), 1), 0) (* Don't need to worry about the first case,
							        * we've already eliminated that one. *)
      and findprefix (a::b, str, lentoprefix) =
	  if (String.isPrefix a str)
	     then lentoprefix
	  else
	      findprefix (b, str, lentoprefix)
	| findprefix (_, "", lentoprefix) =
	  lentoprefix
	| findprefix ([], str, lentoprefix) =
	  findprefix (seperatorlist, strdrop (str, 1), lentoprefix + 1)
      and strdrop (s, n) = implode (sdrop (explode s, n))
      and strtake (s, n) = implode (stake (explode s, n))
      and stake ([], _) = nil
	| stake (a::b, 0) = nil
	| stake (a::b, n) = a :: stake (b, n - 1)
      and sdrop ([], _) = nil
	| sdrop (a::b, 0) = a::b
	| sdrop (a::b, n) = sdrop (b, n - 1)
  in
      List.filter (fn x => not ("" = x)) (cutwhite (splitstr (string, nil)))
  end;

val ts = scanner ["a","b","c"] Char.isSpace;

(* Simplistic parser for first order logic:
 * FOL:
 *   Formula ::= <Quantifier>
 *   Quantifier ::= (<"@"|"!">variable)<Implies>
 *   Implies ::=  <Disjunctive>("=>"<Implies>)
 *   Disjunctive ::= <Conjunctive>("|"<Disjunctive>)
 *   Conjunctive ::= <Literal>("&"<Conjunctive>)
 *   Literal ::= ("~")<Atom>
 *   Atom ::= [string] "(" [simplexlist] ")" | "(" <Implies> ")"
 *   simplexlist ::= (Function|Variable|Constant)
 *   Function ::= [string] "(" [simplexlist] ")"
 *   Variable ::= string that begins with a lowercase letter
 *   Constant ::= string that begins with an uppercase letter
 *)

structure FOLParser =
  struct
  local open FOLSyntax
  in
  val folseplist = ["@", "!", "=>", "!", "&", "~", "(", ")", ",", ";", " "]
  and foliswhite = Char.isSpace;
  val tokenizefol = scanner folseplist foliswhite

  fun parsesimlist (s::"("::rest, args) =
      let
	  val (arglist, r) = parsesimlist (rest, nil)
      in
	  parsesimlist (r,args@[Function(s,arglist)])
      end
    | parsesimlist (")"::x, args) =
      (args, x)
    | parsesimlist (","::x, args) =
      parsesimlist (x, args)
    | parsesimlist (nil, args) =
      (args,nil)
    | parsesimlist (x::r, args) =
      let
	  val var = isvar x
	  val (a::_) = r
      in
	  if not ((a = ",") orelse (a = ")"))
	     then raise Parser_Exn (r, "Expecting a comma or closing parenthesis")
	  else if var then parsesimlist (r, args@[Variable(x)])
		      else parsesimlist (r, args@[Constant(x)])
      end
  and
  parseatom ("("::rest) =
      let
	  val (temptree, r) = parseimplies rest
	  val (first::n) = r
      in
	  if not(first = ")")
	     then raise Parser_Exn (r, "Matching parenthesis required")
	     else (temptree, n)
      end
    | parseatom (predicate::"("::l) =
      let
	  val (arglist, rest) = parsesimlist (l, nil)
      in
	  (Predicate(predicate,arglist), rest)
      end
    | parseatom (n) = raise Parser_Exn (n, "No formula specified")
  and
  isvar (str:string) =
    let
	val (firstchar::_) = (explode str)
    in
      if Char.isLower firstchar
	 then true
	 else false
    end
  and
  parseliteral ("~"::rest) =
      let
	  val (temptree, r) = parseatom rest
      in
	  (Negation(temptree), r)
      end
    | parseliteral (other) = parseatom other
  and
  parseconjunctive (x:string list) =
      let
	  val (temptree, rest) = parseliteral x;
      in
	  if (hd rest) = "&"
	     then (let val (_::n) = rest val (t, r) = parseconjunctive n
		in (Conj(temptree, t), r) end)
	     else (temptree, rest)
      end
  and
  parsedisjunctive (x:string list) =
      let
	  val (temptree, rest) = parseconjunctive x
	  val (first::n) = rest
      in
	  if first = "|"
	     then (let val (t, r) = parsedisjunctive n
		in (Disj(temptree, t), r) end)
	     else (temptree, rest)
      end
  and
  parseimplies (x:string list) =
      let
	  val (temptree, rest) = parsedisjunctive x;
	  val (first::n) = rest
      in
	  if first = "=>"
	     then
	       (let val (t, r) = parseimplies n
	       in (Implies(temptree, t), r)
	       end)
	     else (temptree, rest)
      end
  and
  parsequantifier ("@"::var::rest) = All(var, parsequantifier rest)
    | parsequantifier ("!"::var::rest) = Exists(var, parsequantifier rest)
    | parsequantifier (";"::_) = raise Parser_Exn ([";"], "No formula specified")
    | parsequantifier (other) = (#1 (parseimplies(other)))
  and
  parsewfferror (formula:string) =
      let
	  val tokenlist = (tokenizefol formula @ [";"])
      in
	  (SOME (parsequantifier tokenlist))
      end
      handle Parser_Exn (a,b) => (print ("Error in FOL Parser: " ^ b ^ "\n"); NONE)
  and
  getformula (SOME (f:formula)) = f
    | getformula (NONE) = raise Option.Option
  and
  parsewff (formula:string) = getformula (parsewfferror formula);
  
  end
  end;

(* A simple implementation of propositional logic.
 * PropL:
 *     Equivalent ::= <Implies> ("==" <Equivalent>)
 *     Implies ::= <Disjunctive> ("=>" <Implies>)
 *     Disjunctive ::= <Conjunctive> ("|" <Disjunctive>)
 *     Conjunctive ::= <Equals> ("&" <Conjunctive>)
 *     Equals ::= <Literal> ("=" <Equals>)
 *     Literal ::= ("~")<Proposition|"("<Equivalent>")">
 *     Proposition ::= [string]
 *)

structure PropLParser =
  struct
      local
	  open PropLSyntax
      in
      val proplseplist = ["==", "=>", "|", "&", "=", "~", "(", ")", ";", "T", "F", " "]
      and propliswhite = Char.isSpace;
      val tokenizepropl = scanner proplseplist propliswhite;
      
      fun parsewff (x:string) =
	  SOME (#1 (parseequivalent ((tokenizepropl x) @ [";"])))
	  handle Parser_Exn (a, b) => (print ("Error in Propositional Logic parser: " ^ b ^ "\n"); NONE)
      and getformula (SOME (f:formula)) = f
	| getformula (NONE) = raise Option.Option
      and parseequivalent (x:string list) =
	  let
	      val (temptree, rest) = parseimplies x;
	      val (first::n) = rest
	  in
	      if first = "=="
		 then
		  (let val (t, r) = parseequivalent n
		   in (Equivalence(temptree, t), r)
		   end)
		  else (temptree, rest)
	  end
      and
      parseimplies (x:string list) =
          let
	      val (temptree, rest) = parsedisjunctive x;
	      val (first::n) = rest
	  in
	      if first = "=>"
		 then
		  (let val (t, r) = parseimplies n
		   in (Implies(temptree, t), r)
		   end)
		  else (temptree, rest)
	  end
      and
      parsedisjunctive (x:string list) = 
          let
	      val (temptree, rest) = parseconjunctive x;
	      val (first::n) = rest
	  in
	      if first = "|"
		 then
		  (let val (t, r) = parsedisjunctive n
		   in (Disj(temptree, t), r)
		   end)
		  else (temptree, rest)
	  end
      and
      parseconjunctive (x:string list) =
          let
	      val (temptree, rest) = parseequals x;
	      val (first::n) = rest
	  in
	      if first = "&"
		 then
		  (let val (t, r) = parseconjunctive n
		   in (Conj(temptree, t), r)
		   end)
		  else (temptree, rest)
	  end
      and
      parseequals (x:string list) =
          let
	      val (temptree, rest) = parseliteral x;
	      val (first::n) = rest
	  in
	      if first = "="
		 then
		  (let val (t, r) = parseequals n
		   in (Equals(temptree, t), r)
		   end)
		  else (temptree, rest)
	  end
      and
      parseliteral ("~"::rest) =
	  let
	      val (temptree, r) = parseatom rest
	  in
	      (Negation(temptree), r)
	  end
	| parseliteral (other) = parseatom other
      and
      parseatom ("("::r) =
	  let
	      val (temptree, rest) = parseequivalent r;
	      val (first::n) = rest
	  in
	      if first = ")"
		 then
		  (temptree, n)
		  else raise Parser_Exn (n, "Expecting a closing parenthesis")
	  end
      | parseatom ("T"::r) = (BoolVal(True), r)
      | parseatom ("F"::r) = (BoolVal(False), r)
      | parseatom (proposition::r) = (Proposition (proposition), r)
      | parseatom (n) = raise Parser_Exn (n, "No formula specified");
      end
  end;
