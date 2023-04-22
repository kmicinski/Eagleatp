(* A simple datastructure to represent a table
 * By Kristopher Micinski,
 * For the Eagle Logic System / ATP
 * This is fun, functional, and small
 *)

type ('a, ''b) table = ('a * ''b) list;

structure Table =
  struct
  val niltable = nil;
  
  exception Table;
  
  fun insert (data, identifier, table) = (data, identifier)::table;
  
  fun remove (identifier, nil) = nil
    | remove (identifier, (d,id)::tl) = if id = identifier then tl else (d,id)::(remove (identifier, tl));
  
  fun find (identifier, nil) = raise Table
    | find (identifier, (d,id)::tl) = if id = identifier then d else find (identifier, tl);
  
  end;

(* I found that there is some really wierd nesting taking
 * place with the construction of tables (for example
 * in the inference rule structures). I think this operator
 * should help -- Kris, Aug 28, 2007
 *)
infixr tabcons;

fun ((data:'a, identifier:''b) tabcons (table:('a, ''b) table)) = Table.insert(data, identifier, table);
