open ASTD_B;;
open ASTD_astd;;


let rec getLoopArrowsNewElem state arrows =
  match arrows with
  | [] -> []
  | a::l ->
  	if (ASTD_arrow.get_from a = ASTD_arrow.get_to a) && ASTD_arrow.get_from a = state then
  		ASTD_astd.elem_of ((ASTD_arrow.get_from a)^(ASTD_label.string_of (ASTD_arrow.get_label_transition a)))::getLoopArrowsNewElem state l
  	else
  		getLoopArrowsNewElem state l
  		
let rec transformLoopArrows state arrows =
  match arrows with
  | [] -> []
  | a::l ->
  	if (ASTD_arrow.get_from a = ASTD_arrow.get_to a) && ASTD_arrow.get_from a = state then
  		let new_node_name = (ASTD_arrow.get_from a)^(ASTD_label.string_of (ASTD_arrow.get_label_transition a)) in
  		let b =
    		if ASTD_arrow.is_local a then
    		    [(ASTD_arrow.local_arrow (ASTD_arrow.get_from a)
    		                            (new_node_name)
    		                            (ASTD_arrow.get_transition a)
    		                            (ASTD_arrow.get_predicates a)
    		                            (ASTD_arrow.get_from_final_state a))
    		    ; (ASTD_arrow.local_arrow  new_node_name
    		                                new_node_name
    		                                (ASTD_arrow.get_transition a)
    		                                (ASTD_arrow.get_predicates a)
    		                                false)]
    		else
    		  []
  		  in
  		b@transformLoopArrows state l
  	else
  		a::transformLoopArrows state l;;

let rec arrowsFromNewElem newElem arrow =
  match newElem with
    | [] -> []
    | a::l ->
      (match arrow with
        |ASTD_arrow.Local (from_state, to_state, transition, predicate_list, from_final_state) -> 
          (ASTD_arrow.local_arrow (ASTD_astd.get_name a)
                                  to_state
                                  transition
                                  predicate_list
                                  from_final_state)
          :: (arrowsFromNewElem l arrow)
(*        |From_sub (from_state, to_state, through_state, transition, predicate._list, from_final_state) -> []*)
(*        |To_sub (from_state, to_state, through_state, transition, predicate_list, from_final_state) -> [])*)
      )
      
let rec addArrowsFromNewElem newElem state arrows =
  match arrows with
    | [] -> []
    | a::l ->
      if (ASTD_arrow.get_from a = state) && (ASTD_arrow.get_to a <> state) then
        (arrowsFromNewElem newElem a)@(addArrowsFromNewElem newElem state l)
      else
        addArrowsFromNewElem newElem state l;;

(* Returns the list of the Elem contained in a list of ASTDs *)
let rec getElemsFromSubASTDs astds =
  match astds with
    | [] -> []
    | a::l ->
      (match a with
        | Elem (_) -> a::(getElemsFromSubASTDs l)
        | Automata (_, sub_astds, _, _, _, _) -> (getElemsFromSubASTDs sub_astds)@(getElemsFromSubASTDs l)
        | _ -> failwith "getElemsFromSubASTDs argument must be a list of Elem and Automata");;

(* Returns the arrows needed to convert an ASTD Automata into a DFA/NFA *)
let rec convertArrowsToLocal arrows =
  match arrows with
    | [] -> []
    | a::l ->
      (match a with
        | Elem (_) -> a::(getElemsFromSubASTDs l)
        | Automata (_, sub_astds, _, _, _, _) -> (getElemsFromSubASTDs sub_astds)@(getElemsFromSubASTDs l)
        | _ -> failwith "getElemsFromSubASTDs argument must be a list of Elem and Automata");;

let rec minimize astd = 
	match astd with
    | Elem (astd_name) -> ASTD_astd.elem_of astd_name
    
    | Automata (astd_name, sub_astds, arrows, shallow_final_names, deep_final_names, init_name) ->
      let min_sub_astds = List.map minimize sub_astds in
      ASTD_astd.automata_of astd_name min_sub_astds arrows shallow_final_names deep_final_names init_name
      
    | Sequence (astd_name, left_sub_astd, right_sub_astd) ->
      let min_left_sub_astd = minimize left_sub_astd in
      let min_right_sub_astd = minimize right_sub_astd in
      ASTD_astd.automata_of astd_name
                            ((ASTD_astd.get_sub min_left_sub_astd)@(ASTD_astd.get_sub min_right_sub_astd))
                            ((ASTD_astd.get_arrows min_left_sub_astd)@(ASTD_astd.get_arrows min_right_sub_astd))
                            []
                            (ASTD_astd.get_deep_final min_right_sub_astd)
                            (ASTD_astd.get_init min_left_sub_astd)

    | Choice (astd_name, left_sub_astd, right_sub_astd) ->
      let min_left_sub_astd = minimize left_sub_astd in
      let min_right_sub_astd = minimize right_sub_astd in
      ASTD_astd.automata_of astd_name
                            ((ASTD_astd.get_sub min_left_sub_astd)@(ASTD_astd.get_sub min_right_sub_astd))
                            ((ASTD_astd.get_arrows min_left_sub_astd)@(ASTD_astd.get_arrows min_right_sub_astd))
                            []
                            ((ASTD_astd.get_deep_final min_left_sub_astd)@(ASTD_astd.get_deep_final min_right_sub_astd))
                            (ASTD_astd.get_init min_left_sub_astd)

    | Kleene (astd_name, sub_astd) -> 
  		begin
  			match sub_astd with
  			  | Automata (name, sub_astdList, arrows, shallowFinalList, deepFinalList, init) ->
  					ASTD_astd.automata_of name
  					                      ((getLoopArrowsNewElem init arrows)@sub_astdList)
  					                      ((transformLoopArrows init arrows)@(addArrowsFromNewElem (getLoopArrowsNewElem init arrows) init arrows))
  					                      shallowFinalList
  					                      deepFinalList
  					                      init
  		end;

    | Synchronisation (astd_name, transition_labels, left_sub_astd, right_sub_astd) -> ASTD_astd.elem_of "Synchronisation"
    
(*    | Fork of astd_name * ASTD_label.t list * ASTD_predicate.t list * t * t*)
    
    | QChoice (astd_name, variable, domain, sub_astd) -> ASTD_astd.elem_of "QChoice"

    | QSynchronisation (astd_name, variable, domain, transition_labels, sub_astd) -> ASTD_astd.elem_of "QSynchronisation"   

(*    | QFork of astd_name * ASTD_variable.t * string * ASTD_predicate.t list * ASTD_label.t list * t*)

    | Guard (astd_name, predicates, sub_astd) -> ASTD_astd.elem_of "Guard"

    | Call (astd_name, called_astd_name, var_values_vector) -> ASTD_astd.elem_of "Call"

	
