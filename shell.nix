let pinned-nixpkgs-path = import ./pinned-nixpkgs.nix;
    pinned-pkgs = import pinned-nixpkgs-path {};
in { pkgs ? pinned-pkgs }: # if I ever need to override stuff

with pkgs;

mkShell {
  buildInputs = [
    fstar z3
  ];
}
