(** NB: This is a modified implementation from http://canonical.org/~kragen/sw/dev3/mukanren.ml 
    - Additions:
        - support list terms
        - add thunk unwrapping and truncating
        - swapping order of inputs in mplus for breadth exploration
        - some printers
*)

(* A translation into OCaml of Hemann and Friedman’s interpreter for the
 * tiny relational language μKanren:
 * <http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf>.  It’s
 * slightly less code (36 lines instead of 39), maybe asymptotically more
 * efficient, and I think noticeably easier to understand.
 *)

module Index = Int ;;        (* The type of logic variable indices *)

module Env = Map.Make(Index) (* maps logic variables to terms *)
 
type var  = Var of (Index.t [@printer (fun fmt -> Format.fprintf fmt "%d")])  (* the index is a counter typically from call_fresh *)
[@@deriving show, ord]

(* TODO: function from term to term and lists *)
type term = Vart of var | Const of int | Pair of term * term | TList of term list
[@@deriving show, ord]
;;

type env  = term Env.t
;;

(* Compute what the value of the given term in s is, which may be an
 * unbound var *)
let rec walk (s : env) = function
  | Vart (Var x) when Env.mem x s -> walk s (Env.find x s)
  | u -> u

(* Extend an environment with a new binding *)
and ext_s (Var x) (v : term) (s : env) = Env.add x v s

(* Compute under what conditions u and v can unify given s *)
and unify (u : term) (v : term) (s : env) = match walk s u, walk s v with
    | u', v' when u' = v' -> Some s       (* when they are the same, or *)
    | Vart u', v' -> Some (ext_s u' v' s) (* when either is a variable, *)
    | u', Vart v' -> Some (ext_s v' u' s) (* which we can bind to the other, or *)
    | Pair(ua, ud), Pair(va, vd) -> (match unify ua va s with
        | Some s' -> unify ud vd s'         (* when they are pairs *)
        | None -> None)                     (* whose respective members unify *)
    | Pair(ua, ud), TList(x :: y) -> (match unify ua x s with
        | Some s' -> unify ud (TList y) s'  (* when they are pairs *)
        | None -> None)
    | TList(x :: y), Pair(ua, ud) -> (match unify ua x s with
        | Some s' -> unify ud (TList y) s'  (* when they are pairs *)
        | None -> None)
    | TList u', TList v' ->
        (match (u', v') with 
            | [], [] -> Some s
            | x :: x' :: [], y :: y' :: [] -> 
                (match unify x y s with 
                    | Some s' -> 
                        unify x' y' s'
                    | _ -> 
                        None
                )
            | x :: x', y :: y' -> 
                (match unify x y s with 
                    | Some s' -> 
                        unify (TList x') (TList y') s'
                    | _ -> 
                        None
                )
            | _ -> 
                None
        )
    | _ -> None

type 'a stream = Cons of 'a * 'a stream | Thunk of (unit -> 'a stream) | Mzero
[@@deriving show]
;;

(* Monad plus: merge two streams *)
let rec mplus (t : 'a stream) = function
  | Mzero -> t (* If the second stream is empty, return the first stream *)
  | Thunk f -> Thunk (fun () -> mplus (f()) t) (* η⁻¹-delay and swap *)
  | Cons(e, s) -> Cons(e, mplus s t)  (* or simply recurse if eager - swap order to allow exploration! *)

(* Monad bind: transform stream with g *)
and bind (g : 'a -> 'a stream) = function
  | Mzero   -> Mzero
  | Thunk t -> Thunk (fun () -> bind g (t()))
  | Cons(e, s) -> mplus (g e) (bind g s)

(* Lift a state (or other point) into the stream monad - also called unit *)
and just s = Cons(s, Mzero)        (* `unit` in Hemann and Friedman *)

type state = State of env * Index.t (* index of the next variable to create *)
type goal = state -> state stream

let joinpairs bindfn items = 
  let rec recur g2 = 
      (match g2 with 
      | [] -> failwith "unreachable!! at least 2 goals needed!"
      | g :: [] -> g
      | g :: g' :: [] -> (fun t -> bindfn g' g) 
      | g :: rem -> (fun t -> bindfn g (recur rem))
      )
  in (bindfn (List.hd items) (recur @@ List.tl items)) 
;;

let joinpairsseq bindfn items = 
  let rec recur g1 = 
      (match Seq.uncons g1 with 
      | Some(g, g2) -> 
            (
                match Seq.uncons g2 with
                | Some (g', rem) -> 
                        (
                            if Seq.is_empty rem then 
                                (fun t -> bindfn g g') 
                            else
                                (fun t -> bindfn g (recur g2))
                        )
                | None -> 
                    g
            )
      | None -> failwith "unreachable!! at least 2 goals needed!"
      )
  in (bindfn (fst @@ Option.get @@ Seq.uncons @@ (Seq.take 1 items)) (recur @@ (Seq.drop 1 items))) ;;

(* Disjunction and conjunction of goals *)
let rec
    disj      (g1: goal) (g2 : goal) (t : state)  = mplus (g1 t) (g2 t) and
    disj_many (g1: goal list) (t: state)          = joinpairs (fun x y -> disj x y t) g1 and
    disj_seq  (g1: goal Seq.t) (t: state)         = joinpairsseq (fun x y -> disj x y t) g1 and
    conj      (g1 : goal) (g2 : goal) (t : state) = bind g2 (g1 t) and 
    conj_many (g1: goal list) (t: state)          = joinpairs (fun x y -> conj x y t) g1  and
    conj_seq  (g1: goal Seq.t) (t: state)         = joinpairsseq (fun x y -> conj x y t) g1

(* Supply a fresh logic variable to a goal-returning function *)
(* <Scheme> I’m relentlessly monomorphic *)
and call_fresh (f : term -> goal) (State(e, c)) =
  (f (Vart (Var c))) (State (e, Index.succ c))    (* <OCaml>  hold my beer. *)

(* Create a goal that two things unify, normally called ≡ *)
let match_goal (u : term) (v : term) (State (s, c)) = match unify u v s with
  | Some s' -> just (State (s', c))
  | None -> Mzero


(* The μKanren kernel proper corresponds to what is above.  What is
 * below is “properly the purview of the end user” to Hemann and
 * Friedman.  I have my doubts about this re-adjudication.
 * “Minimizing of the responsibilities of the kernel and pushing all
 * that can be into user space loosens coupling ... and helps
 * eliminate inappropriate intimacy among submodules”?  Okay but all
 * this “user space code” here is dealing with the variable index
 * type, the environment type, and the particular way η⁻¹-delaying of
 * streams is implemented.  This feels like tight coupling and
 * inappropriate intimacy.
 *)

let rec empty_state = State(Env.empty, Index.zero)
and stream_fold (f : 'a -> state -> 'a) (acc: 'a) = function
  | Mzero      -> (acc)
  | Thunk t    -> stream_fold f acc (t ())
  | Cons(e, s) -> stream_fold f (f acc e) s
and stream_iter (f : state -> unit) = function
  | Mzero -> ()
  | Thunk t -> stream_iter f (t())
  | Cons(e, s) -> f(e); stream_iter f s
and string_of_index (c : Index.t) = "$" ^ string_of_int (c)
and string_of_term = function
  | Vart (Var c) -> string_of_index c
  | Const k -> string_of_int k
  | Pair(a, d) -> "(" ^ string_of_term a ^ " " ^ string_of_tail d
  | TList l ->   "[ " ^ (String.concat ", " (List.map (string_of_term) l)) ^ "] "
and string_of_tail = function
  | Pair(a, d) -> string_of_term a ^ " " ^ string_of_tail d
  | t -> ". " ^ string_of_term(t) ^ ")"
and dump_state (State(e, c)) =
  print_string ("next = " ^ string_of_index c ^ " {") ;
    print_newline () ;
  Env.iter (fun i v ->
        print_endline("    " ^ string_of_index i ^ " = " ^ string_of_term v)) e; 
    print_string ("}");
    print_newline ()
and dump_stream (s : state stream) = stream_iter dump_state s
and fives x = disj (match_goal x (Const 5)) (fives x)
and lazy_fives x =
    disj (match_goal x (Const 5)) (fun s -> Thunk(fun () -> (lazy_fives x) s))
and lazy_sixes x =
    disj (match_goal x (Const 6)) (fun s -> Thunk(fun () -> (lazy_sixes x) s))
and pull = function 
  | Thunk t -> 
        (match t () with 
        | (Cons (s, s'))  ->
            Some (s, s')
        | Thunk _ as t' -> 
           pull t'
        | Mzero -> 
            None
        )
  | Cons (s, s') -> Some (s, s')
  | Mzero -> None
and take n s = 
(* NB: works with disjoints. conj will go into a loop  - see examples *)
    if  n = 0 then 
        (* truncate the rest *)
        Mzero
    else 
       (match pull s with 
       | Some (sta, str) ->
            Cons (sta, (take (n-1) str))
       | None -> 
            s
       )
and null (s : state) = Mzero            (* a goal that always fails *)
and disjn = function
  | [] -> null
  | goal::goals -> disj goal (disjn goals)
and nuts (s : state) = just s        (* a goal that always succeeds *)
and conjn = function
  | [] -> nuts
  | goal::goals -> conj goal (conjn goals)

(* A goal that succeeds if v is one of `terms` *)
and amb (terms : term list) (v : term) = match terms with 
  | [] -> null
  | term::ts -> disj (match_goal v term) (amb ts v)
;;

(*
Example usage:

$ ocamlc mukanren.ml && ocaml mukanren.cmo
open Mukanren ;;

call_fresh (fun q -> match_goal q (Const 5)) empty_state ;;
(* - : Mukanren.stream = Cons (State (<abstr>, 1l), Mzero) *)

dump_stream (call_fresh (fun q -> match_goal q (Const 5)) empty_state) ;;
(* next = $1 *)
(* $0 = 5 *)
(* - : unit = () *)

dump_stream (call_fresh (fun q -> match_goal (Pair (q, q)) (Const 5)) empty_state) ;;
(* - : unit = () *)

dump_stream (call_fresh (fun q -> match_goal (Pair (q, q)) (Pair (Const 5, Const 5))) empty_state) ;;
(* next = $1 *)
(* $0 = 5 *)
(* - : unit = () *)

dump_stream (call_fresh (fun q -> match_goal (Pair (q, q)) (Pair (Const 6, Const 5))) empty_state) ;;
(* - : unit = () *)

dump_stream (call_fresh (fun q -> match_goal q (Pair (Const 6, Pair(Const 0, Const 5)))) empty_state) ;;
(* next = $1 *)
(* $0 = (6 0 . 5) *)
(* - : unit = () *)

dump_stream (conj (call_fresh (fun a -> match_goal a (Const 7)))
                  (call_fresh (fun b -> disj (match_goal b (Const 5))
                                             (match_goal b (Const 6)))) empty_state) ;;
(* next = $2 *)
(* $0 = 7 *)
(* $1 = 6 *)
(* next = $2 *)
(* $0 = 7 *)
(* $1 = 5 *)
(* - : unit = () *)

call_fresh fives empty_state ;;
(* Stack overflow during evaluation (looping recursion?). *)

call_fresh lazy_fives empty_state ;;
(* - : Mukanren.stream = Thunk <fun> *)

This next one needs to be interrupted with ^C:

dump_stream (call_fresh lazy_fives empty_state) ;;
    next = $1
    $0 = 5
    next = $1
    $0 = 5
    ...
    Interrupted.


call_fresh (fun f -> disj (lazy_fives f) (lazy_sixes f) ) empty_state |> take 5 |> dump_stream;;
    next = $1 {
        $0 = 6 
    }
    next = $1 {
        $0 = 5
    }
    next = $1 {
        $0 = 6
    }
    next = $1 {
        $0 = 5
    }
    next = $1 {
        $0 = 6
    }
    - : unit = ()

(* will go into a loop *)
call_fresh (fun f -> conj (lazy_fives f) (lazy_sixes f) ) empty_state |> take 5 |> dump_stream;;
    ...
    Interrupted.

dump_stream (call_fresh (amb [Const 17; Pair(Const 20, Const 20); Const 11]) empty_state) ;;
(* next = $1 *)
(* $0 = 11 *)
(* next = $1 *)
(* $0 = (20 . 20) *)
(* next = $1 *)
(* $0 = 17 *)
(* - : unit = () *)

*)
