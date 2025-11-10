{ pkgs ? import <nixpkgs> {config.allowUnfree = true;}}:
pkgs.mkShell {
  packages = [
    pkgs.coq
    pkgs.coqPackages.vscoq-language-server
    pkgs.coqPackages.stdlib
    ];
}