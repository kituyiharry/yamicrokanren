open Munkanren;;

module VMap = Map.Make (String);;
module VSet = Set.Make (struct 
    type t      = term
    let compare = compare_term
end)

module Database = struct 


    type rule = {
        name:   string 
    ;   arity:  int 
    ;   rulefn: (term array -> state -> state stream) (* term list are arguments in reverse order *)
    }

    type t = {
        (* TODO: best if mutable?? *)
        facts: (VSet.t) VMap.t (* Map to a set of ground facts *)
    ;   rules: (rule)   VMap.t
    }

    let empty = {
        facts = VMap.empty
    ;   rules = VMap.empty
    }

    let fact name variable db = 
        { db with facts=(VMap.update name (function 
            | Some vset -> 
                Some (VSet.add variable vset)
            | None   -> 
                Some (VSet.singleton variable)
            ) db.facts) 
        }
    ;;

    (** convert relations into kanren primitives *)
    let relation name argvar db init =
        (  
            (VMap.find name db.facts)
            |> VSet.to_list
            |> (function 
                | [] -> 
                    Mzero
                | variable :: [] -> 
                    (*let _ = assert (List.is_empty @@ List.tl args) in*)
                    (match_goal (argvar) (variable)) init
                | varlist -> (
                    (varlist
                        (* variable can be substituted for any of these variables *)
                        |> List.map (fun v ->
                            (match_goal argvar v)
                        )
                        (*|> List.map (fun (x, y) -> (match_goal x y)) (* build eq goals for unification *)*)
                        |> disj_many
                    ) init
                )
            )
        ) 
    ;;

    (** convert relations into kanren primitives *)
    let multirelation name argvarlist db init =
        (  
            (VMap.find name db.facts)
            |> VSet.to_list
            |> (function 
                | [] -> 
                    Mzero
                | variable :: [] -> 
                    (*let _ = assert (List.is_empty @@ List.tl args) in*)
                    (argvarlist
                        |> List.map (fun a -> (a, variable))
                        |> List.map (fun (x, y) -> (match_goal x y)) (* build eq goals for unification *)
                        |> disj_many
                    ) init
                    (*(match_goal (argvar) (variable)) init*)
                | varlist -> (
                    (varlist
                        (* variable can be substituted for any of these variables *)
                        |> List.map (fun v -> (List.map (fun v' -> (v, v')) argvarlist))
                        |> List.concat
                        |> List.map (fun (x, y) -> (match_goal x y)) (* build eq goals for unification *)
                        |> disj_many
                    ) init
                )
            )
        ) 
    ;;

    (** create a rule *)
    let define name arity rulefn db = 
        { db with rules=(
            VMap.add name ({ name; arity; rulefn; }) db.rules
        )}
    ;;

    (** apply a rule *)
    let apply name args db curstate = 
        let ruleset = VMap.find name db.rules in 
        let _ = assert (Array.length args >= ruleset.arity) in
        ruleset.rulefn args curstate
    ;;

end

