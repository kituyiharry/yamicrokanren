open Munkanren;;

module StringTable = Map.Make (String);;

module Relations = struct

    type t = { 
        mutable seed: int
    ;   tbl    : (string, int) Hashtbl.t
    ;   tables : (string list) StringTable.t
    ;   schemas: (string list) StringTable.t
    }


    let empty = 
        { 
            seed   = 0
        ;   tbl    = (Hashtbl.create 16)
        ;   tables = (StringTable.empty)
        ;   schemas= (StringTable.empty)
        }
    ;;

    let _unique_key table y = 
        (table ^ "_" ^ y)
    ;;

    (* INFO: join table name and column for a unique key!!! *)
    let create table columns state = 
        let count = ref 0 in
        let _ = List.iteri (fun x y -> 
            let _ = (Hashtbl.add state.tbl (_unique_key table y) (state.seed + x))
            in incr count
        ) columns in
        { 
            state with  
            seed  = (state.seed + !count)
            ;   tables = (StringTable.add table [] state.tables)
            ;   schemas= (StringTable.add table columns state.schemas)
        }
    ;;

    (** TODO: simplify - maybe use other struct *)
    let insert table values state = 
        (match StringTable.find_opt table state.tables with
        | Some data ->
            (match StringTable.find_opt table state.schemas with
                | Some vals -> 
                    (if List.length vals = List.length values then
                        Ok ({ state with tables =(StringTable.add table (data @ values) state.tables) })
                    else
                       Error ("Incorrect number of values")
                    )
                | None   -> Error "Table not foound in schema" 
            )
        | _ ->
            Error "Table does not exist"
        )
    ;;

    let table_relation table args state = 
        StringTable.find table state.tables
        |> List.map (fun y -> 
            (List.map (fun x -> 
                (match_goal (Vart (Var (Hashtbl.find state.tbl (_unique_key table y)))) x)
            )) args
            |> (function 
                | one :: [] -> one 
                | rest      -> conj_many rest
            )
        )
        |> (function 
            | a :: [] -> a
            | rest    -> disj_many rest
        )
    ;;

end
