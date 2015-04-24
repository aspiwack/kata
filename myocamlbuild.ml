open Ocamlbuild_plugin
open Command

let () = dispatch begin function
  | After_rules ->
    begin
      flag ["ocaml";"doc";"keep_code"] (S [ A "-keep-code"]);
    end
  | _ -> ()
end
