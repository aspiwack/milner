

let rec take n l =
  match n,l with
  | n , a::l when n > 0 -> a::take (n-1) l
  | _ -> []

let rec drop n l =
  match n,l with
  | n, _::l when n > 0 -> drop (n-1) l
  | _,l -> l

let unflatten ll l =
  snd begin
    List.fold_left begin fun (l',acc) q ->
      let n = List.length q in
      drop n l' , acc@[take n l']
    end (l,[]) ll
  end

module type Tac = sig

  type goal
  type thm

end


module Make (T:Tac) : sig

  type validation = T.thm list -> T.thm
  type tactic = T.goal -> (T.goal list * validation)

  val nop : tactic
  val (<*>) : tactic -> tactic -> tactic

  val (</>) : tactic -> tactic list -> tactic

  val fail : tactic
  val (||) : tactic -> tactic -> tactic

  val ttry : tactic -> tactic
  val repeat : tactic -> tactic
end = struct

  type validation = T.thm list -> T.thm
  type tactic = T.goal -> (T.goal list * validation)

  let nop_proof [thm] = thm
  let nop g = ([g] , nop_proof)

  let then_proof pr prs gss l =
    pr (List.map2 (fun f x -> f x) prs (unflatten gss l))

  let (</>) t1 tl g =
    let (gs,pr) = t1 g in
    let (gss,prs) = List.split (List.map2 (fun f x -> f x) tl gs) in
    List.flatten gss , then_proof pr prs gss

  let (<*>) t1 t2 g =
    let (gs,pr) = t1 g in
    let (gss,prs) = List.split (List.map t2 gs) in
    List.flatten gss , then_proof pr prs gss

  let fail g = failwith "Tactic failure"

  let (||) t1 t2 g =
    try t1 g
    with _ -> t2 g

  let ttry t = t || nop

  let rec repeat t g =
    match
      try Some (t g)
      with _ -> None
    with
    | Some gp -> ((fun _ -> gp) <*> repeat t) g
    | None -> nop g

end
