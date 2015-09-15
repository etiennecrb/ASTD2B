open ASTD_B;;
open ASTD_astd;;
open ASTD_arrow;;

(* Return the list of the names of all Elem for converting Kleene to Automata,
including those which needs to be created *)
let rec kleeneTransformElems init_name final_names arrows =
  match arrows with
  | [] -> []
  | a::l ->
  	if (get_from a = get_to a) && List.exists (function state -> state = (get_from a)) (init_name::final_names) then
  		(elem_of ((get_from a)^"_"^(ASTD_label.string_of (get_label_transition a))))::kleeneTransformElems init_name final_names l
  	else
  	  if (get_to a = init_name) && List.exists (function state -> state = (get_from a)) final_names then
    	  (elem_of ((get_from a)^"_"^(ASTD_label.string_of (get_label_transition a))))::kleeneTransformElems init_name final_names l
    	else
    	  kleeneTransformElems init_name final_names l

(* Return the list of the needed arrows for converting Kleene to Automata
to remove loop arrows for the init state *)
let rec kleeneTransformArrowsInit init_name arrowsFromInit arrows =
  match arrows with
  | [] -> []
  | a::l ->
  	if (get_from a = get_to a) && (init_name = (get_from a)) then
  		let new_node_name = init_name^"_"^(ASTD_label.string_of (get_label_transition a)) in
  		let b = [(local_arrow init_name
    		                    (new_node_name)
    		                    (get_transition a)
    		                    (get_predicates a)
    		                    false)
    		    ; (local_arrow  new_node_name
    		                    new_node_name
    		                    (get_transition a)
    		                    (get_predicates a)
    		                    false)]
  		  in
  		let c = List.map (function arrow -> local_arrow new_node_name
  		                                                (get_to arrow)
  		                                                (get_transition arrow)
  		                                                (get_predicates arrow)
  		                                                false) arrowsFromInit
  		  in
  		b@c@(kleeneTransformArrowsInit init_name arrowsFromInit l)
  	else
  		a::kleeneTransformArrowsInit init_name arrowsFromInit l

(* Return the list of the needed arrows for converting Kleene to Automata
to remove loop arrows for a final state *)
let rec kleeneTransformArrowsFinal final_name arrowsToFinal arrows =
  match arrows with
  | [] -> []
  | a::l ->
  	if (get_from a = get_to a) && (final_name = (get_from a)) then
  		let new_node_name = (get_from a)^"_"^(ASTD_label.string_of (get_label_transition a)) in
  		let b = [(local_arrow new_node_name
    		                    final_name
    		                    (get_transition a)
    		                    (get_predicates a)
    		                    false)
    		    ; (local_arrow  new_node_name
    		                    new_node_name
    		                    (get_transition a)
    		                    (get_predicates a)
    		                    false)]
  		  in
  		let c = List.map (function arrow -> local_arrow new_node_name
  		                                                (get_to arrow)
  		                                                (get_transition arrow)
  		                                                (get_predicates arrow)
  		                                                false) arrowsToFinal
  		  in
  		b@c@(kleeneTransformArrowsFinal final_name arrowsToFinal l)
  	else
  		a::kleeneTransformArrowsFinal final_name arrowsToFinal l
  		
(* Return the list of the needed arrows for converting Kleene to Automata
to remove arrows from a final state to init *)
let rec kleeneTransformArrowsFromFinalToInit init_name final_name arrowsToFinal arrows =
  match arrows with
  | [] -> []
  | a::l ->
  	if (get_from a = final_name) && (get_to a = init_name) then
  		let new_node_name = (get_from a)^"_"^(ASTD_label.string_of (get_label_transition a)) in
  		let b = [(local_arrow new_node_name
    		                    final_name
    		                    (get_transition a)
    		                    (get_predicates a)
    		                    false)]
  		  in
  		let c = List.map (function arrow -> local_arrow (get_from arrow)
  		                                                new_node_name
  		                                                (get_transition arrow)
  		                                                (get_predicates arrow)
  		                                                false) arrowsToFinal
  		  in
  		b@c@(kleeneTransformArrowsFromFinalToInit init_name final_name arrowsToFinal l)
  	else
  		a::kleeneTransformArrowsFromFinalToInit init_name final_name arrowsToFinal l
  		
let rec getArrowsFrom state_name arrows =
  match arrows with
    | [] -> []
    | a::l ->
      if (get_from a) = state_name then
        a::(getArrowsFrom state_name l)
      else
        getArrowsFrom state_name l
        
let rec getArrowsTo state_name arrows =
  match arrows with
    | [] -> []
    | a::l ->
      if (get_to a) = state_name then
        a::(getArrowsTo state_name l)
      else
        getArrowsTo state_name l

let rec kleeneTransformArrowsFinals final_names arrows =
  match final_names with
  | [] -> arrows
  | a::l -> kleeneTransformArrowsFinal a (getArrowsTo a arrows) (kleeneTransformArrowsFinals l arrows)
  
let rec kleeneTransformArrowsFromFinalsToInit init_name final_names arrows =
  match final_names with
  | [] -> arrows
  | a::l -> kleeneTransformArrowsFromFinalToInit init_name a (getArrowsTo a arrows) (kleeneTransformArrowsFromFinalsToInit init_name l arrows)

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

(* Return a list of ASTDs without those whose names are in the given list *)
let rec removeASTDs astds_to_remove astds =
  match astds with
    | [] -> []
    | a:: l ->
      if List.exists (function name -> (get_name a) = name) astds_to_remove then
        removeASTDs astds_to_remove l
      else
        a :: (removeASTDs astds_to_remove l)

(* Return the given arrows where those targeting to an element of destinations
are redirected to new_destination
!! Modified arrows are returned as Local arrows !! *)
let rec changeArrowsDestination destinations new_destination arrows =
  match arrows with
    | [] -> []
    | a::l ->
      if List.exists (function name -> (get_to a) = name) destinations then
        (local_arrow   (get_from a)
                      new_destination
                      (get_transition a)
                      (get_predicates a)
                      false) :: (changeArrowsDestination destinations new_destination l)
      else
        a :: (changeArrowsDestination destinations new_destination l)

(* Return the given arrows where those from an element of origins
are redirected from new_origin
!! Modified arrows are returned as Local arrows !! *)
let rec changeArrowsOrigin origins new_origin arrows =
  match arrows with
    | [] -> []
    | a::l ->
      if List.exists (function name -> (get_from a) = name) origins then
        (local_arrow   new_origin
                      (get_to a)
                      (get_transition a)
                      (get_predicates a)
                      false) :: (changeArrowsOrigin origins new_origin l)
      else
        a :: (changeArrowsOrigin origins new_origin l)

let kleeneTransformArrows init_name final_names arrows =
  let temp_arrows1 = kleeneTransformArrowsInit init_name (getArrowsFrom init_name arrows) arrows in
  let temp_arrows2 = kleeneTransformArrowsFinals final_names temp_arrows1 in
  let temp_arrows3 = kleeneTransformArrowsFromFinalsToInit init_name final_names temp_arrows2 in
  let temp_arrows4 = changeArrowsDestination final_names init_name temp_arrows3 in
  changeArrowsOrigin final_names init_name temp_arrows4

(* Converting NFAs to DFAS *)
let convertNFAtoDFA astd =
  match astd with
    | Automata(astd_name, sub_astds, arrows, shallow_final_names, deep_final_names, init_name) ->
      astd
    | _ -> astd

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

    | Kleene (astd_name, sub_astd) ->
      let min_sub_astd = minimize sub_astd in
      let deep_final_names = get_deep_final min_sub_astd in
      let shallow_final_names = get_shallow_final min_sub_astd in
      let init_name = get_init min_sub_astd in
      let arrows = get_arrows min_sub_astd in
      let new_arrows = kleeneTransformArrows init_name (shallow_final_names@deep_final_names) arrows in
      (* Merge init state and final states *)
      automata_of astd_name
                  ((kleeneTransformElems init_name (deep_final_names@shallow_final_names) arrows)
                  @(removeASTDs (deep_final_names@shallow_final_names) (get_sub min_sub_astd)))
                  new_arrows
                  [init_name]
  					      []
  					      init_name

    | Synchronisation (astd_name, transition_labels, left_sub_astd, right_sub_astd) -> astd
    
    | Fork (astd_name, transition_labels, predicates, left_sub_astd, right_sub_astd) -> astd
    
    | QChoice (astd_name, variable, domain, sub_astd) -> astd

    | QSynchronisation (astd_name, variable, domain, transition_labels, sub_astd) -> astd  

    | QFork  (astd_name, variable, domain, predicates, transition_labels, sub_astd) -> astd

    | Guard (astd_name, predicates, sub_astd) -> astd

    | Call (astd_name, called_astd_name, var_values_vector) -> astd
    
    | _ -> failwith "minimize argument must be an ASTD"

	
