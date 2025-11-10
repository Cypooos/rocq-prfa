{ pkgs ? import <nixpkgs> {config.allowUnfree = true;}}:
pkgs.mkShell {
  packages = [ 
    pkgs.ocaml
    (with pkgs.ocamlPackages; [
      findlib
      utop
      core 
    ])
    pkgs.coq
    pkgs.coqPackages.vscoq-language-server
    pkgs.coqPackages.stdlib
    # Required packages from the course
    pkgs.coqPackages.metarocq
    pkgs.coqPackages.equations
    # Add the packages you want!
    # meow meow
    ];
  shellHook = ''
export OCAMLPATH="$(echo $ROCQPATH):$OCAMLPATH"
'';
}