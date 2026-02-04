open Yamicrokanren.Munkanren;;
open Yamicrokanren.Database;;
open Family;;

let () =
    let _ = (
        (*call_fresh (fun q -> match_goal q (Const 5)) empty_state*)
        (* - : Mukanren.stream = Cons (State (<abstr>, 1l), Mzero) *)

        (*let _ = dump_stream (call_fresh (fun q -> match_goal q (Const 5)) empty_state) in*)
        (* next = $1 *)
        (* $0 = 5 *)
        (* - : unit = () *)
        (*let _ = Format.printf "1. ============================================\n" in*)

        (*let _ = dump_stream (call_fresh (fun q -> match_goal (Pair (q, q)) (Const 5)) empty_state) in*)
        (* - : unit = () *)
        (*let _ = Format.printf "2.============================================\n" in*)
        
        (*let _ = dump_stream (call_fresh (fun q -> match_goal (Pair (q, q)) (Pair (Const 5, Const 5))) empty_state) in*)
        (* next = $1 *)
        (* $0 = 5 *)
        (* - : unit = () *)
        (*let _ = Format.printf "3.============================================\n" in*)

        (*let _ = dump_stream (call_fresh (fun q -> match_goal (Pair (q, q)) (Pair (Const 6, Const 5))) empty_state) in*)
        (* - : unit = () *)
        (*let _ = Format.printf "4.============================================\n" in*)

        (*let _ = dump_stream (call_fresh (fun q -> match_goal q (Pair (Const 6, Pair(Const 0, Const 5)))) empty_state) in *)
        (* next = $1 *)
        (* $0 = (6 0 . 5) *)
        (* - : unit = () *)

        (*let _ = dump_stream (conj (call_fresh (fun a -> match_goal a (Const 7))) (call_fresh (fun b -> disj (match_goal b (Const 5)) (match_goal b (Const 6)))) empty_state) in*)
        (* next = $2 *)
        (* $0 = 7 *)
        (* $1 = 6 *)
        (* next = $2 *)
        (* $0 = 7 *)
        (* $1 = 5 *)
        (* - : unit = () *)

        let _ = Format.printf "5.============================================\n" in
        let _ = Format.printf "\nFamily ============================================\n" in

        let fam = 
            FamilyTree.start
            |> FamilyTree.male   "Don" 
            |> FamilyTree.male   "Randy" 
            |> FamilyTree.male   "Papaw"
            |> FamilyTree.female "Rosie" 
            |> FamilyTree.female "Anne" 

            |> FamilyTree.parent "Papaw" "Don"
            |> FamilyTree.parent "Don"   "Randy"
            |> FamilyTree.parent "Don"   "Anne"
            |> FamilyTree.parent "Rosie" "Randy"

            |> FamilyTree.relationship "father" 2 (fun db -> 
                (fun tl cstate -> 
                    (
                        conj_many [
                            Database.relation "male"   (tl.(0)) db
                        ;   Database.relation "parent" (Pair (tl.(0), tl.(1))) db
                        ] cstate
                    )
                )
            )
            |> FamilyTree.relationship "grandparent" 2 (fun db -> 
                (fun tl cstate -> 
                    (
                        call_fresh (fun mid -> 
                            conj_many ([
                                Database.relation "parent" (Pair (tl.(0), mid)) db;  
                                Database.relation "parent" (Pair (mid, tl.(1))) db;  
                            ])
                        )
                    ) cstate
                )
            )
            (*|> FamilyTree.parent "Rosie" "Anne"*)
        in

        let _ = Format.printf "\nMale   ============================================\n" in
        let _ = 
            (FamilyTree.query (Database.relation "male") fam |> List.iter (Fun.compose print_newline print_string))
        in
        let _ = Format.printf "\nFemale ============================================\n" in
        let _ = 
            (FamilyTree.query (Database.relation "female") fam |> List.iter (Fun.compose print_newline print_string))
        in
        let _ = Format.printf "\nParent ============================================\n" in
        let _ = 
            (FamilyTree.query (Database.relation "parent") fam |> List.iter (Fun.compose print_newline print_string))
        in
        let _ = Format.printf "\nParent - Child ============================================\n" in
        let _ = 
            (FamilyTree.query (fun t db ->
                    call_fresh (fun t' -> 
                        conj_many (
                            [
                                Database.multirelation "parent" [ t'; t ] db
                            ;   (match_goal t (Pair (t, t')))
                            ]
                        )
                    )
            ) fam |> List.iter (Fun.compose print_newline print_string))
        in
        let _ = Format.printf "\nRandys Mother ============================================\n" in
        let _ = 
            (FamilyTree.query (fun t db ->
                     (*parent of randy who is female *)
                    conj_many (
                        [
                            Database.relation "parent" (Pair (t, Const (FamilyTree.seed "Randy" fam))) db
                        ;   Database.relation "female" t db
                        ]
                    )
            ) fam |> List.iter (Fun.compose print_newline print_string))
        in
        let _ = Format.printf "\nRandys Father  ============================================\n" in
        let _ = 
            (FamilyTree.query (fun t db ->
                call_fresh (fun t' -> 
                    Database.apply "father" [| t; (Const (FamilyTree.seed "Randy" fam)) |] db
                )
            ) fam |> List.iter (Fun.compose print_newline print_string))
        in

        let _ = Format.printf "\nGrandparents ============================================\n" in
        let _ = 
            (* NOTE: You will need to filter out intermediate values when reifying *)
            (FamilyTree.query (fun t db ->
                call_fresh (fun u -> 
                    call_fresh (fun v -> 
                        (conj
                            (Database.apply "grandparent" [| u; v |] db)
                            (match_goal t (Pair (u,v)))
                        )
                    )
                );
            )) fam |> List.iter (Fun.compose print_newline print_string)
        in
        ()

    ) in

    ()


