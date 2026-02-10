open Yamicrokanren.Munkanren;;
open Yamicrokanren.Database;;
open Family;;

let () =
    let _ = (
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
        in

        let _ = Format.printf "\nMale   ============================================\n" in
        let _ = 
            (FamilyTree.query (Fun.id) (Database.relation "male") fam |> List.iter (Fun.compose print_newline print_string))
        in
        let _ = Format.printf "\nFemale ============================================\n" in
        let _ = 
            (FamilyTree.query (Fun.id) (Database.relation "female") fam |> List.iter (Fun.compose print_newline print_string))
        in
        let _ = Format.printf "\nParent ============================================\n" in
        let _ = 
            (FamilyTree.query (Fun.id) (Database.relation "parent") fam |> List.iter (Fun.compose print_newline print_string))
        in
        let _ = Format.printf "\nParent - Child ============================================\n" in
        let _ = 
            (FamilyTree.query (Fun.id) (Database.relation "parent") fam |> List.iter (Fun.compose print_newline print_string))
        in
        let _ = Format.printf "\nRandys Mother ============================================\n" in
        let _ = 
            (FamilyTree.query (Fun.id) (fun t db ->
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
            (FamilyTree.query (Fun.id) (fun t db ->
                call_fresh (fun t' -> 
                    Database.apply "father" [| t; (Const (FamilyTree.seed "Randy" fam)) |] db
                )
            ) fam |> List.iter (Fun.compose print_newline print_string))
        in

        let _ = Format.printf "\nGrandparents ============================================\n" in
        let _ = 
            (* NOTE: You will need to filter out intermediate values when reifying *)
            (FamilyTree.query (Env.filter (fun _ -> function 
                (* filter other intermediate values *)
                | Pair _ -> true
                | _      -> false
                )
            ) (fun t db ->
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

        let rec appendo l r out =
            disj 
                (conj (match_goal l (TList [])) (match_goal r out))
                (call_fresh (fun a -> 
                    (call_fresh (fun d -> 
                        (call_fresh (fun res -> 
                            conj
                                (match_goal l (Pair (a, d)))
                                (conj   
                                    (match_goal out (Pair (a, res)))
                                    (appendo d r res)
                                )
                        ))
                    ))
                )
            )
        in

        let _ = Format.printf "\n=========================================================\n" in
        let _ = Format.printf "\n=========================================================\n" in

        (* Test appendo *)

        let _ = dump_stream @@ call_fresh (fun x -> 
            appendo (TList [ (Const 1); (Const 3) ]) (TList [ (Const 2) ]) x
        ) empty_state in

 
        ()

    ) in

    ()


