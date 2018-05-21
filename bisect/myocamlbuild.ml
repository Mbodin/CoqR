open Ocamlbuild_plugin
open Ocamlbuild_pack

let ocamlfind_query pkg =
  let cmd = Printf.sprintf "ocamlfind query %s" (Filename.quote pkg) in
  Ocamlbuild_pack.My_unix.run_and_open cmd (fun ic ->
    Ocamlbuild_pack.Log.dprintf 5 "Getting Ocaml directory from command %s" cmd;
      input_line ic)

let path_to_bisect = ocamlfind_query "bisect"

let () =
  dispatch begin function
    | After_rules ->
      flag ["bisect"; "pp"]
        (S [A "camlp4o"; A "str.cma"; A (path_to_bisect ^ "/bisect_pp.cmo")]) ;
      flag ["bisect"; "compile"]
        (S [A "-I"; A path_to_bisect]) ;
      flag ["bisect"; "link"; "byte"]
        (S [A "-I"; A path_to_bisect; A "bisect.cma"]) ;
      flag ["bisect"; "link"; "native"]
        (S [A "-I"; A path_to_bisect; A "bisect.cmxa"]) ;
      flag ["bisect"; "link"; "java"]
        (S [A "-I"; A path_to_bisect; A "bisect.cmja"])
    | _ -> ()
  end

