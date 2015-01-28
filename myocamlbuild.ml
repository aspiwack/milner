open Ocamlbuild_plugin

let _ = dispatch @@ function
  | Before_options -> 
      
      Options.use_ocamlfind := true;
      Options.ocaml_cflags  := ["-w";"-a"]
        (* suppresses warnings *)

  | _ -> ()
