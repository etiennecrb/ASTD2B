open ASTD_B;;
open ASTD_astd;;
open ASTD_arrow;;

(* A set structure for ASTD with lexicographic order as order relation *)
module ASTDSet = Set.Make(struct
                            type t = ASTD_astd.t
                            let compare a b = compare (get_name a) (get_name b)
                          end);;



(* =============================================== *)
(* ==================== Utils ==================== *)
(* =============================================== *)


(* Remove duplicates in a list *)
let rec removeDuplicates l =
  match l with
    | [] -> []
    | a::l -> if List.mem a l then removeDuplicates l else a::(removeDuplicates l)
    | _ -> failwith "removeDuplicates expects a list as argument"

(* Concat all elements of a list of string *)
let rec fromListToString l =
  match l with
    | [] -> ""
    | a::l -> (get_name a)^(fromListToString l)
    | _ -> failwith "fromListToString expects a list of string as argument"



(* =============================================== *)
(* ======== ASTD Transformation functions ======== *)
(* =============================================== *)


(* Return an equivalent automata where init state has only exit transitions
and no entry one (except if it also a shallow final state) and any final state
has only entry transitions and no exit one (except if it is an init state).

Argument must be a Automata ASTD with Elem sub-ASTDs only *)
let rec simplifyInitFinals automata =
  let isToTransform arrow =
    ((get_to arrow = get_init automata) && not(List.mem (get_init automata) (get_shallow_final automata)))
    ||  (not((get_from arrow = get_init automata)) && List.mem (get_from arrow) (get_shallow_final automata)) in
  let arrows_to_transform = List.filter isToTransform (get_arrows automata) in
  
  match arrows_to_transform with
    | [] -> automata (* Job completed *)
  	
    | a::l ->
      (* One elementary state is added for a concerned state *)
      (* Several arrows to be transformed share the same new state *)
      let new_elem_name = if (get_to a) = (get_init automata) then (get_to a)^"Bis" else (get_from a)^"Bis" in
      
      (* Rerouting the a arrow to the new state *)
      let rerouted_arrows = 
        let from_state = if (get_to a) = (get_init automata) then get_from a else new_elem_name in
        let to_state = if (get_to a) = (get_init automata) then new_elem_name else get_to a in
        ((local_arrow from_state to_state (get_transition a) (get_predicates a) false)
          :: (List.filter (function arrow -> not(arrow = a)) (get_arrows automata)))
      in
      
      (* Adding to the new state the same successors as init state *)
      (* or the same predecessors as the final state *)
      let new_arrows = 
        if (get_to a) = (get_init automata) then
          List.map (function arrow -> local_arrow new_elem_name (get_to arrow) (get_transition arrow) (get_predicates arrow) false)
            (List.filter (function arrow -> (get_from arrow) = (get_to a)) (get_arrows automata))
        else
          List.map (function arrow -> local_arrow (get_from arrow) new_elem_name (get_transition arrow) (get_predicates arrow) false)
            (List.filter (function arrow -> (get_to arrow) = (get_from a)) (get_arrows automata))
      in
      
      (* Since a new state and new arrows are added each time there is an arrow
      to be transformed, we must remove duplicates in sub-ASTDs and arrows lists *)
      simplifyInitFinals (automata_of   (get_name automata)
                                        (removeDuplicates ((elem_of new_elem_name)::(get_sub automata)))
                                        (removeDuplicates (rerouted_arrows@new_arrows))
                                        (get_shallow_final automata)
                                        (get_deep_final automata)
                                        (get_init automata))


(* Return the kleene closure of the given automata

Argument must be a Automata ASTD with Elem sub-ASTDs only *)
let rec kleeneClosure name automata =
  (* Simplifying init and final states to perform merging *)
  let automata = simplifyInitFinals automata in
  
  (* Merge final and init states *)
  let sub_astds = List.filter (function astd ->
                                not( List.mem (get_name astd) ((get_shallow_final automata)@(get_deep_final automata))
                              )
                              (get_sub automata)
  in
  
  (* Rerouting entry transitions from finals to init *)
  let arrows = List.map (function arrow ->
                          if List.mem (get_to arrow) ((get_shallow_final automata)@(get_deep_final automata)) then
                            local_arrow (get_from arrow) (get_init automata) (get_transition arrow) (get_predicates arrow) false
                          else
                            arrow
                        )
                        (get_arrows automata)
  in
  
  automata_of kleene_name sub_astds arrows [(get_init automata)] [] (get_init automata)
  	

(* Return an equivalent automata with a unique final state

Argument must be a Automata ASTD with Elem sub-ASTDs only *)
let rec mergeFinals automata =
  let automata = simplifyInitFinals automata in
  
  (* Merge final states and naming it as the fist shallow final *)
  let shallow_final = List.hd (get_shallow_final automata) in
  let sub_astds = List.filter (function astd -> not( List.mem (get_name astd) (List.tl (get_shallow_final automata))))
                              (get_sub automata)
  in
  (* Rerouting arrows from any final state to the unique one *)
  let arrows = List.map (function arrow ->
                          if List.mem (get_to arrow) (get_shallow_final automata) then
                            local_arrow (get_from arrow) shallow_final (get_transition arrow) (get_predicates arrow) false
                          else
                            arrow
                        )
                        (get_arrows automata)
  in
      
  automata_of (get_name automata) sub_astds arrows [shallow_final] [] (get_init automata)


(* Convert the sub-ASTDs of an Automata to Elem ASTD

The sub-ASTDs must be Automata with Elem sub-ASTDs *)
let rec automataTransform automata =
  let sub_astds = get_sub automata in
  let astds_to_transform = List.filter (function astd -> match astd with | Elem (_) -> false | _ -> true) sub_astds in
  
  match astds_to_transform with
    | [] -> automata
    | a::l ->
      let new_elems = get_sub a in
      let rerouteArrow arrow =
        if (get_from arrow) = (get_name a) || (get_to arrow) = (get_name a) then
          match arrow with
            | Local (from_name, to_name, transition, predicates, is_final) ->
              if (get_from arrow) = (get_name a) then
                List.map (function state -> local_arrow (get_name state) to_name transition predicates is_final)
                  (List.filter (function state -> not(is_final) || List.mem (get_name state) ((get_shallow_final a)@(get_deep_final a))) (get_sub a))
              else
                [local_arrow from_name (get_init a) transition predicates is_final]
            | From_sub (from_name, to_name, through_name, transition, predicates, is_final) ->
              if through_name = (get_name a) then
                [local_arrow from_name to_name transition predicates is_final]
              else
                [local_arrow from_name (get_init a) transition predicates is_final]
            | To_sub (from_name, to_name, through_name, transition, predicates, is_final) ->
              if through_name = (get_name a) then
                [local_arrow from_name to_name transition predicates is_final]
              else
                List.map (function state -> local_arrow (get_name state) to_name transition predicates is_final)
                  (List.filter (function state -> not(is_final) || List.mem (get_name state) ((get_shallow_final a)@(get_deep_final a))) (get_sub a))
        else
          [arrow]
      in
      let elems = new_elems@(List.filter (function astd -> not(astd = a)) sub_astds) in
      let arrows = (get_arrows a)@(List.concat (List.map rerouteArrow (get_arrows automata))) in
      let init_name = if (get_init automata) = (get_name a) then get_init a else get_init automata in
      let shallow_final =
        if List.mem (get_name a) (get_shallow_final automata) then
          (List.map get_name (get_sub a))
          @ (List.filter (function elem -> not((get_name a) = elem)) (get_shallow_final automata))
        else if List.mem (get_name a) (get_deep_final automata) then
          (get_deep_final a) @ (get_shallow_final a) @ (get_shallow_final automata)
        else
          (get_shallow_final automata)
      in
      
      let deep_final = List.filter (function elem -> not((get_name a) = elem)) (get_deep_final automata) in
      
      automataTransform (automata_of  (get_name automata)
                                      elems
                                      arrows
                                      (get_shallow_final automata)
                                      (get_deep_final automata)
                                      init_name)


(* Loop of the determinization algorithm *)
let rec determinize_step nfa dfa stack =
  match stack with
    | [] -> dfa
    | a::l ->
      let arrows = List.filter (function arrow -> List.mem (get_from arrow) (List.map get_name (ASTDSet.elements a))) (get_arrows nfa) in
      let arrow_types = List.map (function arrow -> ((get_transition arrow), (get_predicates arrow))) arrows in
      let arrow_types = removeDuplicates arrow_types in
      let list_of_new_elems = 
        List.map (  function arrow_type ->
                      (* Storing all successors of a in a list *)
                      let destinations_list = (
                        List.map (function arrow -> find_subastd (get_to arrow) (get_sub nfa))
                          (List.filter (function arrow -> 
                            if (get_transition arrow) = (fst arrow_type) && (get_predicates arrow) = (snd arrow_type) then
                              true
                            else
                              false
                            )
                            arrows
                          )
                        )
                      in
                      (* Creating a set out of the list *)
                      List.fold_right ASTDSet.add destinations_list ASTDSet.empty
                  ) arrow_types
        in
      let new_stack_elems = List.filter (function elem_set -> not(List.mem (fromListToString (ASTDSet.elements elem_set)) (List.map get_name (get_sub dfa)))) (removeDuplicates list_of_new_elems) in
      let new_arrows = 
        List.map (  function arrow_type ->
                      let destinations_list = (
                        List.map (function arrow -> find_subastd (get_to arrow) (get_sub nfa))
                          (List.filter (function arrow -> 
                            if (get_transition arrow) = (fst arrow_type) && (get_predicates arrow) = (snd arrow_type) then
                              true
                            else
                              false
                            )
                            arrows
                          )
                        )
                      in
                      let destinations_set = ASTDSet.elements (List.fold_right ASTDSet.add destinations_list ASTDSet.empty) in
                      local_arrow (fromListToString (ASTDSet.elements a)) (fromListToString destinations_set) (fst arrow_type) (snd arrow_type) false
                  ) arrow_types
      in
      let new_shallow_final = List.filter (function elem -> List.exists (function e -> List.mem (get_name e) (get_shallow_final nfa)) (ASTDSet.elements elem)) new_stack_elems in
      let new_deep_final = List.filter (function elem -> List.exists (function e -> List.mem (get_name e) (get_deep_final nfa)) (ASTDSet.elements elem)) new_stack_elems in
      let dfa = automata_of (get_name dfa)
                            ((get_sub dfa)@(List.map (function elem -> elem_of (fromListToString (ASTDSet.elements elem))) new_stack_elems))
                            ((get_arrows dfa)@new_arrows)
                            ((get_shallow_final dfa)@(List.map (function elem -> fromListToString (ASTDSet.elements elem)) new_shallow_final))
                            ((get_deep_final dfa)@(List.map (function elem -> fromListToString (ASTDSet.elements elem)) new_deep_final))
                            (get_init dfa)
      in
      determinize_step nfa dfa (l@new_stack_elems)


let determinize nfa =
  let shallow_final = if List.mem (get_init nfa) (get_shallow_final nfa) then [get_init nfa] else [] in
  let deep_final = if List.mem (get_init nfa) (get_deep_final nfa) then [get_init nfa] else [] in
  let dfa = automata_of (get_name nfa)
                        [elem_of (get_init nfa)]
                        []
                        shallow_final
                        deep_final
                        (get_init nfa)
  in
  determinize_step nfa dfa [ASTDSet.singleton (find_subastd (get_init nfa) (get_sub nfa))]


let reverse automata =
  let automata = simplifyFinals automata in
  automata_of (get_name automata)
              (get_sub automata)
              (List.map (function a -> local_arrow (get_to a) (get_from a) (get_transition a) (get_predicates a) false)
                (get_arrows automata))
              [(get_init automata)]
              []
              (List.hd (get_shallow_final automata))
              
              
let brzozowski automata =
  determinize (reverse ((determinize (reverse automata))))


let rec minimize astd = 
	match astd with
    | Elem (astd_name) -> elem_of astd_name
    
    | Automata (astd_name, sub_astds, arrows, shallow_final_names, deep_final_names, init_name) ->
      let min_sub_astds = List.map minimize sub_astds in (* Now all sub ASTDs are Elem or Automata with Elem sub ASTDs *)
      let nfa = automataTransform (automata_of astd_name min_sub_astds arrows shallow_final_names deep_final_names init_name) in
      brzozowski nfa
      
    | Sequence (astd_name, left_sub_astd, right_sub_astd) -> astd

    | Choice (astd_name, left_sub_astd, right_sub_astd) -> astd

    | Kleene (astd_name, sub_astd) ->
      let min_sub_astd = minimize sub_astd in
      let nfa = kleeneTransform astd_name min_sub_astd in
      brzozowski nfa

    | Synchronisation (astd_name, transition_labels, left_sub_astd, right_sub_astd) -> astd
    
    | Fork (astd_name, transition_labels, predicates, left_sub_astd, right_sub_astd) -> astd
    
    | QChoice (astd_name, variable, domain, sub_astd) -> astd

    | QSynchronisation (astd_name, variable, domain, transition_labels, sub_astd) ->
      QSynchronisation (astd_name, variable, domain, transition_labels, minimize sub_astd)

    | QFork  (astd_name, variable, domain, predicates, transition_labels, sub_astd) ->
      QFork (astd_name, variable, domain, predicates, transition_labels, minimize sub_astd)

    | Guard (astd_name, predicates, sub_astd) -> astd

    | Call (astd_name, called_astd_name, var_values_vector) -> astd
    
    | _ -> failwith "minimize argument must be an ASTD"

	
