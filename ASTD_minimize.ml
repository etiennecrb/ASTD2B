open ASTD_B;;
open ASTD_astd;;
open ASTD_arrow;;


(*let rec getLoopArrowsNewElem state arrows =*)
(*  match arrows with*)
(*  | [] -> []*)
(*  | a::l ->*)
(*  	if (get_from a = get_to a) && get_from a = state then*)
(*  		elem_of ((get_from a)^(ASTD_label.string_of (get_label_transition a)))::getLoopArrowsNewElem state l*)
(*  	else*)
(*  		getLoopArrowsNewElem state l*)
(*  		*)
(*let rec transformLoopArrows state arrows =*)
(*  match arrows with*)
(*  | [] -> []*)
(*  | a::l ->*)
(*  	if (get_from a = get_to a) && get_from a = state then*)
(*  		let new_node_name = (get_from a)^(ASTD_label.string_of (get_label_transition a)) in*)
(*  		let b =*)
(*    		if is_local a then*)
(*    		    [(local_arrow (get_from a)*)
(*    		                            (new_node_name)*)
(*    		                            (get_transition a)*)
(*    		                            (get_predicates a)*)
(*    		                            (get_from_final_state a))*)
(*    		    ; (local_arrow  new_node_name*)
(*    		                                new_node_name*)
(*    		                                (get_transition a)*)
(*    		                                (get_predicates a)*)
(*    		                                false)]*)
(*    		else*)
(*    		  []*)
(*  		  in*)
(*  		b@transformLoopArrows state l*)
(*  	else*)
(*  		a::transformLoopArrows state l;;*)
(**)
(*let rec arrowsFromNewElem newElem arrow =*)
(*  match newElem with*)
(*    | [] -> []*)
(*    | a::l ->*)
(*      (match arrow with*)
(*        | Local (from_state, to_state, transition, predicate_list, from_final_state) -> *)
(*          (local_arrow (get_name a)*)
(*                                  to_state*)
(*                                  transition*)
(*                                  predicate_list*)
(*                                  from_final_state)*)
(*          :: (arrowsFromNewElem l arrow)*)
(*(*        |From_sub (from_state, to_state, through_state, transition, predicate._list, from_final_state) -> []*)*)
(*(*        |To_sub (from_state, to_state, through_state, transition, predicate_list, from_final_state) -> [])*)*)
(*      )*)
(*      *)
(*let rec addArrowsFromNewElem newElem state arrows =*)
(*  match arrows with*)
(*    | [] -> []*)
(*    | a::l ->*)
(*      if (get_from a = state) && (get_to a <> state) then*)
(*        (arrowsFromNewElem newElem a)@(addArrowsFromNewElem newElem state l)*)
(*      else*)
(*        addArrowsFromNewElem newElem state l;;*)

(* Return the list of the Elem ASTD contained in a list of ASTDs,
the Elem ASTD contained in their sub ASTDs and recursively.

ASTDs and sub ASTDs must be Elem or Automata *)
let rec bringOutElems astds =
  match astds with
    | [] -> []
    | a::l ->
      (match a with
        | Elem (_) -> a::(bringOutElems l)
        | Automata (_, sub_astds, _, _, _, _) -> (bringOutElems sub_astds)@(bringOutElems l)
        | _ -> failwith "bringOutElems argument must be a list of Elem and Automata (0)"
      )
    | _ -> failwith "bringOutElems argument must be a list of Elem and Automata (1)"
      
(* Return the list of the arrows contained in a list of ASTDs,
the arrows contained in their sub ASTDs and recursively.

Given ASTDs and their sub ASTDs must be Elem or Automata *)
let rec bringOutArrows astds =
  match astds with
    | [] -> []
    | a::l ->
      (match a with
        | Elem (_) -> bringOutArrows l
        | Automata (_, sub_astds, arrows, _, _, _) -> arrows@(bringOutArrows sub_astds)@(bringOutArrows l)
        | _ -> failwith "bringOutArrows argument must be a list of Elem and Automata (0)"
      )
    | _ -> failwith "bringOutArrows argument must be a list of Elem and Automata (1)"

(* Transform arrows from an Automata ASTD to local arrows between Elem ASTD
that have the same propertiers.
Given sub ASTDs must be Elem or Automata *)
let rec transformArrowsIntoLocalBetweenElem sub_astds arrows =
  match arrows with
    | [] -> []
    | a::l ->
      (match a with
        | Local (from_state_name, to_state_name, transition, predicates, from_final_state) ->
          let to_state_astd = find_subastd to_state_name sub_astds in
          let from_state_astd = find_subastd from_state_name sub_astds in
          (match to_state_astd with
            | Elem (_) ->
              (match from_state_astd with
                | Elem (_) ->
                  (* Local arrow between Elem ASTD, no changes *)
                  a::(transformArrowsIntoLocalBetweenElem sub_astds l)
                
                | Automata (_, deep_sub_astds_from, _, shallow_final_from, deep_final_from, _) ->
                  (* Local arrow from Automata to Elem *)
                  if from_final_state then
                    (* Transform the arrow into new arrows from shallow and deep final states of Automata to targeted Elem *)
                    ((List.map (function elem_name -> local_arrow elem_name to_state_name transition predicates false) shallow_final_from)
                     @(List.map (function elem_name -> local_arrow elem_name to_state_name transition predicates false) deep_final_from)
                     @(transformArrowsIntoLocalBetweenElem sub_astds l))
                  else
                    (* Transform the arrow into new arrows from all sub ASTDs of Automata to targeted Elem *)
                    ((List.map (function elem -> local_arrow (get_name elem) to_state_name transition predicates false) deep_sub_astds_from)
                     @(transformArrowsIntoLocalBetweenElem sub_astds l))
                | _ -> failwith "transformArrowsIntoLocalBetweenElem sub_astds argument must be Elem or Automata with Elem sub ASTDs"
              )
            | Automata (_, _, _, _, _, init_name_to) ->
              (match from_state_astd with
                | Elem (_) ->
                  (* Local arrow from Elem to Automata *)
                  (* Transform the arrow into a local arrow from Elem to init state of targeted Automata *)
                  (local_arrow from_state_name init_name_to transition predicates false)::(transformArrowsIntoLocalBetweenElem sub_astds l)
                | Automata (_, deep_sub_astds_from, _, shallow_final_from, deep_final_from, _) ->
                  (* Local arrow from Automata to Automata *)
                  if from_final_state then
                    (* Transform the arrow into new arrows from shallow and deep final states of Automata to init state of targeted Automata *)
                    ((List.map (function elem_name -> local_arrow elem_name init_name_to transition predicates false) shallow_final_from)
                     @(List.map (function elem_name -> local_arrow elem_name init_name_to transition predicates false) deep_final_from)
                     @(transformArrowsIntoLocalBetweenElem sub_astds l))
                  else
                    (* Transform the arrow into new arrows from all sub ASTDs of Automata to init state of targeted Automata *)
                    ((List.map (function elem -> local_arrow (get_name elem) init_name_to transition predicates false) deep_sub_astds_from)
                     @(transformArrowsIntoLocalBetweenElem sub_astds l))
                | _ -> failwith "transformArrowsIntoLocalBetweenElem sub_astds argument must be Elem or Automata with Elem sub ASTDs"
              )
            | _ -> failwith "transformArrowsIntoLocalBetweenElem sub_astds argument must be Elem or Automata with Elem sub ASTDs"
          )
          
        | From_sub (from_state_name, to_state_name, through_state_name, transition, predicates, from_final_state) ->
          let to_state_astd = find_subastd to_state_name sub_astds in
          (match to_state_astd with
            | Elem (_) ->
              (* From_sub arrow from Elem to Elem *)
              (* Transform arrow into local arrow *)
              (local_arrow from_state_name to_state_name transition predicates false)::(transformArrowsIntoLocalBetweenElem sub_astds l)
            | Automata (_, _, _, _, _, init_name_to) ->
              (* From_sub arrow from Elem to Automata *)
              (* Transform arrow into local arrow from Elem to init state of targeted Automata *)
              (local_arrow from_state_name init_name_to transition predicates false)::(transformArrowsIntoLocalBetweenElem sub_astds l)
            | _ -> failwith "transformArrowsIntoLocalBetweenElem sub_astds argument must be Elem or Automata with Elem sub ASTDs"
          )
        | To_sub (from_state_name, to_state_name, through_state_name, transition, predicates, from_final_state) ->
          let from_state_astd = find_subastd from_state_name sub_astds in
          (match from_state_astd with
            | Elem (_) ->
              (* To_sub arrow from Elem to Elem *)
              (* Transform arrow into local arrow *)
              (local_arrow from_state_name to_state_name transition predicates false)::(transformArrowsIntoLocalBetweenElem sub_astds l)
            | Automata (_, deep_sub_astds_from, _, shallow_final_from, deep_final_from, _) ->
              (* To_sub arrow from Automata to Elem *)
              if from_final_state then
                (* Transform the arrow into new arrows from shallow and deep final states of Automata to targeted Elem *)
                ((List.map (function elem_name -> local_arrow elem_name to_state_name transition predicates false) shallow_final_from)
                 @(List.map (function elem_name -> local_arrow elem_name to_state_name transition predicates false) deep_final_from)
                 @(transformArrowsIntoLocalBetweenElem sub_astds l))
              else
                (* Transform the arrow into new arrows from all sub ASTDs of Automata to targeted Elem *)
                ((List.map (function elem -> local_arrow (get_name elem) to_state_name transition predicates false) deep_sub_astds_from)
                 @(transformArrowsIntoLocalBetweenElem sub_astds l))
            | _ -> failwith "transformArrowsIntoLocalBetweenElem sub_astds argument must be Elem or Automata with Elem sub ASTDs"
          )
        | _ -> failwith "transformArrowsIntoLocalBetweenElem second argument must be a list of arrows"
      )

(*let rec getArrowsFrom state_name arrows =*)
(*  match arrows with*)
(*    | [] -> []*)
(*    | a::l ->*)
(*      if ((get_from a)=state_name) then*)
(*        a::(getArrowsFrom state_name l)*)
(*      else*)
(*        getArrowsFrom state_name l*)

let rec minimize astd = 
	match astd with
    | Elem (astd_name) -> elem_of astd_name
    
    | Automata (astd_name, sub_astds, arrows, shallow_final_names, deep_final_names, init_name) ->
      let min_sub_astds = List.map minimize sub_astds in (* Now all sub ASTDs are Elem or Automata with Elem sub ASTDs *)
      let init_astd = find_subastd init_name min_sub_astds in
      let new_init_name =
      (match init_astd with
        | Elem (_) -> init_name
        | Automata (_, _, _, _, _, _) -> get_init init_astd
        | _ -> failwith "minimize error: a sub ASTD is not Elem or Automata with Elem sub ASTDs"
      ) in
      automata_of astd_name 
                  (bringOutElems min_sub_astds)
                  ((transformArrowsIntoLocalBetweenElem min_sub_astds arrows)@(bringOutArrows min_sub_astds))
                  shallow_final_names
                  deep_final_names
                  new_init_name
      
    | Sequence (astd_name, left_sub_astd, right_sub_astd) -> elem_of astd_name
(*      let min_left_sub_astd = minimize left_sub_astd in*)
(*      let min_right_sub_astd = minimize right_sub_astd in*)
(*      automata_of astd_name*)
(*                  (min_left_sub_astd@min_right_sub_astd)*)
(*                  ((get_arrows min_left_sub_astd)@(get_arrows min_right_sub_astd))*)
(*                  []*)
(*                  (get_deep_final min_right_sub_astd)*)
(*                  (get_init min_left_sub_astd)*)

    | Choice (astd_name, left_sub_astd, right_sub_astd) -> elem_of astd_name
(*      let min_left_sub_astd = minimize left_sub_astd in*)
(*      let min_right_sub_astd = minimize right_sub_astd in*)
(*      automata_of astd_name*)
(*                            ((get_sub min_left_sub_astd)@(get_sub min_right_sub_astd))*)
(*                            ((get_arrows min_left_sub_astd)@(get_arrows min_right_sub_astd))*)
(*                            []*)
(*                            ((get_deep_final min_left_sub_astd)@(get_deep_final min_right_sub_astd))*)
(*                            (get_init min_left_sub_astd)*)

    | Kleene (astd_name, sub_astd) -> elem_of astd_name
(*  		begin*)
(*  			match sub_astd with*)
(*  			  | Automata (name, sub_astdList, arrows, shallowFinalList, deepFinalList, init) ->*)
(*  					automata_of name*)
(*  					                      ((getLoopArrowsNewElem init arrows)@sub_astdList)*)
(*  					                      ((transformLoopArrows init arrows)@(addArrowsFromNewElem (getLoopArrowsNewElem init arrows) init arrows))*)
(*  					                      shallowFinalList*)
(*  					                      deepFinalList*)
(*  					                      init*)
(*  		end;*)

    | Synchronisation (astd_name, transition_labels, left_sub_astd, right_sub_astd) -> elem_of astd_name
    
    | Fork (astd_name, transition_labels, predicates, left_sub_astd, right_sub_astd) -> elem_of astd_name
    
    | QChoice (astd_name, variable, domain, sub_astd) -> elem_of astd_name

    | QSynchronisation (astd_name, variable, domain, transition_labels, sub_astd) -> elem_of astd_name   

    | QFork  (astd_name, variable, domain, predicates, transition_labels, sub_astd) -> elem_of astd_name

    | Guard (astd_name, predicates, sub_astd) -> elem_of astd_name

    | Call (astd_name, called_astd_name, var_values_vector) -> elem_of astd_name
    
    | _ -> failwith "minimize argument must be an ASTD"

	
