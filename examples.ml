open Logic
open Logic.Tactical
open Logic.Tactic

let a = Atom"A"
let b = Atom"B"
let c = Atom"C"

let (-->) gm x =
  List.fold_right (fun h f -> Impl(h,f)) gm x

let title s = print_newline (); print_endline ("== "^s^" ==")

let example ttl tac g =
  let _ = title ttl in
  match tac g with
  | ([],pr) -> Tactic.print (pr[])
  | exception Failure s -> print_endline ("Tactic failed: "^s)
  | exception _ -> print_endline("Tactic failed")

(** A simple proof *)

let ex1 = [a;[a]-->b] --> b

let _ =
  let t = Tactic.(intro<*>intro<*>elim a</>[id;id]) in
  example "Example 1" t ([],ex1)


(** A decision procedure *)

let push n (gamma,c) =
  let Impl(a,b) = List.nth gamma n in
  (elim b </> [intro<*>weak (n+1);elim a</>[id;id]]) (gamma,c)

let left n (gamma,conc) =
  match List.nth gamma n with
  | Impl(Atom _,_) -> push n (gamma,conc)
  | Impl(Impl(a,b),c) ->
      begin
        elim (Impl(a,b)) </> [
          intro<*>push (n+1)<*>weak 1;
          elim (Impl(b,c)) </> [
            intro<*>weak(n+1);
            intro<*>(elim (Impl(a,b))</>[id;intro<*>id])
          ]
        ]
      end (gamma,conc)

let rec tauto (gamma,c) =
  let simplify = repeat (id||intro) in
  (simplify<*>decide) (gamma,c)
and decide (gamma,c) =
  let all_left = List.mapi (fun i _ -> left i<*>tauto) gamma in
  (List.fold_right (fun a t -> a||t) all_left fail) (gamma,c)

let _ = example "Example 1-2" tauto ([],ex1)

let ex2 =
  let ab = [a] --> b in
  let abc = [a;b] --> c in
  [a;ab;abc] --> c

let _ = example "Example 2" tauto ([],ex2)

let ex3 =
  let f = [a]-->b in
  let fc = [f]-->c in
  [f;fc]-->c

let _ = example "Example 3" tauto ([],ex3)

let ex4 =
  let nn x y = [[x]-->y] --> y in
  let nne x y = [nn x y] --> x in
  let peirce x y = [[[x]-->y]-->x]-->x in
  Impl (nne a b,peirce a b)

let _ = example "Example 4" tauto ([],ex4)
