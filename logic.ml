type atom = string


type formula =
  | Atom of atom
  | Impl of formula*formula

type context = formula list
type goal = context*formula

module Goal = struct

  open PPrint
  open PPrintEngine
  open PPrintCombinators

  let format_formula =
    let rec impl = function
      | Impl(f1,f2) -> infix 2 1 (utf8string "⇒")(atom f1) (atom f2)
      | f -> atom f
    and atom = function
      | Atom a -> string a
      | f -> group @@ parens (impl f)
    in
    impl

  let format_context gamma = group (separate_map (comma^^break 1) format_formula (List.rev gamma))

  let format (gamma,c) =
    group
      (format_context gamma ^^ break 1 ^^ string"⊢"^^ blank 1 ^^format_formula c)

  let format_goals l = separate_map hardline format l

  let print_goals l = ToChannel.pretty 1. 120 stdout (format_goals l)
end

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

  val print : thm -> unit

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


  let rec format pr =
    let open PPrint in
    let open PPrintEngine in
    let sub p =
      hardline^^utf8string"⌜" ^^ align p ^^hardline^^utf8string"⌞"
    in
    match pr with
    | Id -> string"id"
    | Weak (i,pr) -> string"weak"^^blank 1^^OCaml.int i^^hardline^^format pr
    | Intro pr -> string"intro"^^hardline^^format pr
    | Elim(f,pr1,pr2) ->
        group (string"elim"^^blank 1^^Goal.format_formula f)^^sub (format pr1)^^sub (format pr2)^^hardline

  let print (_,pr) =
    let open PPrint in
    let open PPrintEngine in
    ToChannel.pretty 1. 120 stdout (format pr)

end

module G = struct type _goal = goal type goal = _goal type thm = Tactic.thm end

module Tactical = Tactical.Make(G)
