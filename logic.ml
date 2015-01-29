type atom = string


type formula =
  | Atom of atom
  | Impl of formula*formula

type context = formula list
type goal = context*formula

type proof =
  | Id
  | Weak of int * proof
  | Intro of proof
  | Elim of formula * proof * proof


module Tactic : sig
  type thm
  type validation = thm list -> thm
  type tactic = goal -> (goal list * validation)

  val id : tactic
  val weak : int -> tactic
  val intro : tactic
  val elim : formula -> tactic

end = struct
  type thm = goal * proof
  type validation = thm list -> thm
  type tactic = goal -> (goal list * validation)

  let id_proof (gamma,c) [] =
    assert (List.mem c gamma);
    (gamma,c) , Id
  let id (gamma,c) =
    if List.mem c gamma then ([] , id_proof (gamma,c))
    else failwith "Not an assumption"

  let remove i l =
    let r = ref [] in
    let x = ref None in
    List.iteri (fun j a -> if j<>i then r := a::!r else x := Some a) l;
    (!x , List.rev !r)

  let add i x l =
    match i with
    | 0 -> x::l
    | _ ->
      let r = ref [] in
      List.iteri (fun j a -> r := a::!r ; if j=i-1 then r := x::!r) l;
      List.rev !r

  let weak_proof i a [(gamma,b),pr] = ( add i a gamma , b ) , Weak(i,pr)
  let weak i (gamma,a) =
    match remove i gamma with
    | (Some b,gamma') -> ( [(gamma',a)] , weak_proof i b )
    | _ -> failwith"Not a hypothesis"

  let intro_proof [(a::gamma,b),pr] = ( gamma , Impl(a,b) ) , Intro pr
  let intro = function
    | (gamma,Impl(a,b)) -> ( [(a::gamma,b)] , intro_proof )
    | _ -> failwith "Not an implication"

  let elim_proof = function
    | [(gamma,Impl(a,b)),pr1;(gamma',a'),pr2] when a=a' && gamma=gamma' -> (gamma,b) , Elim(a,pr1,pr2)
  let elim a (gamma,b) =
    ( [(gamma,Impl(a,b));(gamma,a)] , elim_proof )

end

module G = struct type _goal = goal type goal = _goal type thm = Tactic.thm end

module Tactical = Tactical.Make(G)
