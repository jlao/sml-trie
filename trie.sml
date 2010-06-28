(* Signature for dictionaries *)
(*
   For simplicity, we assume keys are strings, while stored entries
   are of arbitrary type.  This is prescribed in the signature.

   Existing entries may be "updated" by inserting a new entry
   with the same key.
*)

signature DICT =
sig
  type key = string                 (* concrete type *)
  type 'a entry = key * 'a          (* concrete type *)

  type 'a dict                      (* abstract type *)

  val empty : 'a dict
  val lookup : 'a dict -> key -> 'a option
  val insert : 'a dict * 'a entry -> 'a dict
	val toString : ('a -> string) -> 'a dict -> string
end;  (* signature DICT *)

exception InvariantViolationException

structure Trie :> DICT = 
struct
	type key = string
	type 'a entry = key * 'a

	datatype 'a trie = 
		Root of 'a option * 'a trie list
	| Node of 'a option * char * 'a trie list

	type 'a dict = 'a trie

	val empty = Root(NONE, nil)

	(* val lookup: 'a dict -> key -> 'a option *)
	fun lookup trie key =
		let
			(* val lookupList: 'a trie list * char list -> 'a option *)
			fun lookupList (nil, _) = NONE
			  | lookupList (_, nil) = raise InvariantViolationException
			  | lookupList ((trie as Node(_, letter', _))::lst, key as letter::rest) =
						if letter = letter' then lookup' (trie, rest)
						else lookupList (lst, key)
			  | lookupList (_, _) =
						raise InvariantViolationException

			(*
				val lookup': 'a trie -> char list
			*)
			and lookup' (Root(elem, _), nil) = elem
			  | lookup' (Root(_, lst), key) = lookupList (lst, key)
			  | lookup' (Node(elem, _, _), nil) = elem
			  | lookup' (Node(elem, letter, lst), key) = lookupList (lst, key)
		in
			lookup' (trie, explode key)
		end

	(*
		val insert: 'a dict * 'a entry -> 'a dict
	*)
	fun insert (trie, (key, value)) = 
		let
			(*
				val insertChild: 'a trie list * key * value -> 'a trie list

				Searches a list of tries to insert the value. If a matching letter 
				prefix is found, it peels of a letter from the key and calls insert'. 
				If no matching letter prefix is found, a new trie is added to the list.

				Invariants:
					* key is never nil.
					* The trie list does not contain a Root.
				Effects: none
			*)
			fun insertChild (nil, letter::nil, value) = 
						[ Node(SOME(value), letter, nil) ]
			  | insertChild (nil, letter::rest, value) = 
						[ Node(NONE, letter, insertChild (nil, rest, value)) ]
				| insertChild ((trie as Node(_, letter', _))::lst, key as letter::rest, value) = 
						if letter = letter' then
							insert' (trie, rest, value) :: lst
						else
							trie :: insertChild (lst, key, value)
				| insertChild (Root(_,_)::lst, letter::rest, value) =
						raise InvariantViolationException
				| insertChild (_, nil, _) = (* invariant: key is never nil *)
						raise InvariantViolationException

			(*
				val insert': 'a trie * char list * 'a -> 'a trie

				Invariants:
					* The value is on the current branch, including potentially the current node we're on.
					* If the key is nil, assumes the current node is the destination.
				Effects: none
			*)
			and insert' (Root(_, lst), nil, value) = Root(SOME(value), lst)
				| insert' (Root(elem, lst), key, value) = Root(elem, insertChild (lst, key, value))
				| insert' (Node(_, letter, lst), nil, value) = Node(SOME(value), letter, lst)
				| insert' (Node(elem, letter, lst), key, value) = Node(elem, letter, insertChild (lst, key, value))
		in
			insert'(trie, explode key, value)
		end

		(*
			val toString: ('a -> string) -> 'a dict -> string
		*)
		fun toString (f: 'a -> string) (trie: 'a dict): string =
			let
				val prefix = "digraph trie {\nnode [shape = circle];\n"
				val suffix = "}\n"

				(* val childNodeLetters: 'a trie list * char list -> char list *)
				fun childNodeLetters (lst: 'a trie list, id: char list): char list =
					(foldr 
						(fn (Node(_, letter, _), acc) => letter::acc
							| _ => raise InvariantViolationException) nil lst)

				(* val edgeStmt: string * string -> string *)
				fun edgeStmt (start: string, dest: string, lbl: char) =
					start ^ " -> " ^ dest ^ " [ label = " ^ Char.toString(lbl) ^ " ];\n"

				(* val allEdgesFrom: char list * char list *)
				fun allEdgesFrom (start: char list, lst: char list): string = 
					(foldr 
						(fn (letter, acc) => 
							acc ^ edgeStmt(implode(start), implode(start @ [letter]), letter))
						"" lst)

				(* val labelNode: stirng * string -> string *)
				fun labelNode (id: string, lbl: string) =
					id ^ " [ label = \"" ^ lbl ^ "\" ];\n"

				fun toString' (Root(elem, lst): 'a dict, id: char list): string =
							let
								val idStr = implode(id)
								val childLetters = childNodeLetters(lst, id)
								val childStr = foldr (fn (trie, acc) => acc ^ toString'(trie, id)) "" lst
							in
								(case elem
									of SOME(value) => 
											labelNode (idStr, f(value)) ^ 
											allEdgesFrom (id, childLetters)
									 | NONE => 
											labelNode (idStr, "") ^ 
									 		allEdgesFrom (id, childLetters)) ^ childStr
							end
					| toString' (Node(elem, letter, lst), id) =
							let
								val thisId = id @ [letter]
								val idStr = implode(thisId)
								val childLetters = childNodeLetters(lst, thisId)
								val childStr = foldr (fn (trie, acc) => acc ^ toString'(trie, thisId)) "" lst
							in
								(case elem
									of SOME(value) => 
											labelNode (idStr, f(value)) ^ 
											allEdgesFrom (thisId, childLetters)
									 | NONE => 
											labelNode (idStr, "") ^ 
									 		allEdgesFrom (thisId, childLetters)) ^ childStr
							end
			in
				prefix ^ (toString' (trie, [#"_", #"R"])) ^ suffix
			end
end
