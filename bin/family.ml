open Yamicrokanren.Munkanren;;
open Yamicrokanren.Database;;

module FamilyTree = struct 

    type t = {
        db:   Database.t
    ;   tbl:  (string, int) Hashtbl.t (* interning table - mapping from names to variable ids *)
    ;   log:  string list             (* interning cache - freeze to an array to  *)
    ;   seed: int ref
    }

    module StringSet = Set.Make (String) ;;

    let start = { db=Database.empty; tbl=Hashtbl.create 8; seed=ref 0; log=[] } ;;

    let seed name state = 
        Hashtbl.find state.tbl name 
    ;;

    let add_or_refer_fact name state apply = 
        match Hashtbl.find_opt state.tbl name with
        | Some entr -> 
            apply state entr
        | None -> 
            let _ = incr state.seed in
            let _ = Hashtbl.add state.tbl name !(state.seed) in
            apply { state with log=(name :: state.log) }  !(state.seed)
    ;;

    let male name state = 
        (* TODO: assert relationship is not mutually exclusive *)
        add_or_refer_fact name state (fun state entr -> 
            { state with db=(Database.fact "male" (Const entr) state.db) }
        )
    ;;

    let female name state = 
        add_or_refer_fact name state (fun state entr -> 
            { state with db=(Database.fact "female" (Const entr) state.db) }
        )
    ;;

    (* some may be left hanging - needs to be male or female first but we don't
       account for it now *)
    let parent pname offspring state = 
        add_or_refer_fact pname state (fun state' entr -> 
            add_or_refer_fact offspring state' (fun state'' entr' -> 
                { state with db=(Database.fact "parent" (Pair ((Const entr), (Const entr'))) state''.db) }
            )
        )
    ;;

    let relationship name members (logic: (Database.t -> (term array -> state -> state stream))) state =
        {
            state with db=(Database.define name members (logic state.db) state.db)
        }
    ;;

    let reify envstate y _tblvals = 
        let rec collect term =
            match y with
            | Const seed ->
                _tblvals.(seed-1)
            | Pair (Const left, Const right) -> 
                (Format.sprintf "%s -- %s" _tblvals.(left-1) _tblvals.(right-1))
            | Pair (l, r) -> 
                (match (walk envstate l, walk envstate r) with 
                    | (Const left, Const right) ->
                        (Format.sprintf "%s -- %s"   _tblvals.(left - 1) _tblvals.(right-1))
                    | (Const left, z') -> 
                        (*(Format.sprintf "%s -- (%s)" _tblvals.(left - 1) (collect z'))*)
                        (Format.sprintf "%s -- (%s)" _tblvals.(left - 1) ("->??"))
                    | (z, z') -> 
                        "??-??"
                        (*(Format.sprintf "[%s] -- [%s]" *)
                            (*(collect z ) *)
                            (*(collect z'))*)
                )
            | _ -> 
                "??"
        in collect y
    ;;

    (* Just dumps the env at the end - might want to be more selective ?? *)
    let query reifier logic state = 
        let _tblvals = List.rev state.log |> Array.of_list in
        let _data = (
            (* fold to collect  *)
            stream_fold (fun acc (State (envstate, _bucket)) -> 
                (* this is where we should filter out what variables we care about - in the reification! *)
                Env.fold (fun _  y acc -> (reify envstate y _tblvals) :: acc) (reifier envstate) acc
            ) []
            (*dump_stream @@ *)
            (call_fresh (fun t -> logic t state.db) empty_state) 
        ) in _data
        (*|> StringSet.to_list*)
    ;;


    let dquery logic state = 
        let _tblvals = List.rev state.log |> Array.of_list in
        (* fold to collect  *)
        let _data = ((dump_stream @@ call_fresh (fun t -> logic t state.db) empty_state)) in [] 
        (*|> StringSet.to_list*)
    ;;


end
