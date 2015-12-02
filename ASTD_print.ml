open ASTD_B;;
open ASTD_astd;;
open ASTD_arrow;;

let rec type_astd astd =
  match astd with
    | Elem (astd_name) -> "elem"
    
    | Automata (astd_name, sub_astds, arrows, shallow_final_names, deep_final_names, init_name) ->
      (* States of the automata *)
      let state_format state = "("^(ASTD_astd.get_name state)^" -> "^(type_astd state)^")" in
      let s_states = String.concat ",\n" (List.map state_format sub_astds) in
      
      (* Arrows *)
      let arrow_type_format a =
        if is_local a then
          "(local,"^(get_from a)^","^(get_to a)^")"
        else if is_from_sub a then
          "(from_sub,"^(get_from a)^","^(get_to a)^","^(get_through a)^")"
        else
          "(to_sub,"^(get_from a)^","^(get_to a)^","^(get_through a)^")"
      in
      
      let transition_format t =
        let params = (ASTD_transition.get_params t) in
        match params with
          | [] -> ASTD_label.string_of (ASTD_transition.get_label t)
          | _ -> ( ASTD_label.string_of (ASTD_transition.get_label t))^"("^( ASTD_term.string_of_params params)^")"
      in
      
      let predicate_format p = "["^(ASTD_predicate.string_of p)^"]" in
      let predicates_format p_list = "{"^(String.concat "," (List.map predicate_format p_list))^"}" in
      
      let final_format a = if get_from_final_state a then "True" else "False" in
      
      let arrow_format a = "("^(arrow_type_format a)^","^(transition_format (get_transition a))^","^(predicates_format (get_predicates a))^","^(final_format a)^")" in
      let s_arrows = String.concat ",\n" (List.map arrow_format arrows) in
      
      let s_shallow_final = String.concat "," shallow_final_names in
      let s_deep_final = String.concat "," deep_final_names in
      
      "<aut;\n{"^s_states^"\n};\n{"^s_arrows^"\n};\n{"^s_shallow_final^"};\n{"^s_deep_final^"\n};\n"^init_name^"\n>"
      
    | Sequence (astd_name, left_sub_astd, right_sub_astd) ->
      "<.;\n"^(print_astd left_sub_astd)^"\n;\n"^(print_astd right_sub_astd)^"\n>"
      
    | Choice (astd_name, left_sub_astd, right_sub_astd) ->
      "<|;\n"^(print_astd left_sub_astd)^"\n;\n"^(print_astd right_sub_astd)^"\n>"

    | Kleene (astd_name, sub_astd) ->
      "<*;\n"^(print_astd sub_astd)^"\n>"

    | Synchronisation (astd_name, transition_labels, left_sub_astd, right_sub_astd) ->
      "<|[]|;{"^(String.concat "," transition_labels)^"};\n"^(print_astd left_sub_astd)^"\n;\n"^(print_astd right_sub_astd)^"\n>"
    
    | Fork (astd_name, transition_labels, predicates, left_sub_astd, right_sub_astd) ->
      let predicate_format p = "["^(ASTD_predicate.string_of p)^"]" in
      let predicates_format p_list = "{"^(String.concat "," (List.map predicate_format p_list))^"}" in
      "</|\;{"^(String.concat "," transition_labels)^"};\n"^(predicates_format predicates)^";"^(print_astd left_sub_astd)^"\n;\n"^(print_astd right_sub_astd)^"\n>"
    
    | QChoice (astd_name, variable, domain, sub_astd) ->
      "<|:;"^variable^";"^domain^";"^(print_astd sub_astd)^"\n>"

    | QSynchronisation (astd_name, variable, domain, transition_labels, sub_astd) ->
      "<|[]|:;"^variable^";"^domain^";{"^(String.concat "," transition_labels)^"};\n"^(print_astd sub_astd)^"\n>"

    | QFork  (astd_name, variable, domain, predicates, transition_labels, sub_astd) ->
      let predicate_format p = "["^(ASTD_predicate.string_of p)^"]" in
      let predicates_format p_list = "{"^(String.concat "," (List.map predicate_format p_list))^"}" in
      "</|\:;"^variable^";"^domain^";"^(predicates_format predicates)^";{"^(String.concat "," transition_labels)^"};\n"^(print_astd sub_astd)^"\n>"

    | Guard (astd_name, predicates, sub_astd) ->
      let predicate_format p = "["^(ASTD_predicate.string_of p)^"]" in
      let predicates_format p_list = "{"^(String.concat "," (List.map predicate_format p_list))^"}" in
      "<=>;"^(predicates_format predicates)^";\n"^(print_astd sub_astd)^"\n>"

    | Call (astd_name, called_astd_name, var_values_vector) ->
      let var_values v = (fst v)^"->"^(ASTD_term.string_of (snd v)) in
      "<call;"^called_astd_name^";{"^(String.concat "," (List.map var_values var_values_vector))^"}>"
    
    | _ -> failwith "minimize argument must be an ASTD"

and print_astd astd =
  "("^(get_name astd)^","^(type_astd astd)^"\n)"