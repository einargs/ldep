let pinned-nixpkgs-path = import ./pinned-nixpkgs.nix;
    pinned-pkgs = import pinned-nixpkgs-path {};
in { pkgs ? pinned-pkgs }: # if I ever need to override stuff

let
  z3 = pkgs.z3;
  fstar = pkgs.callPackage ./fstar.nix {};
in pkgs.mkShell {
  buildInputs = [
    fstar
    z3
  ];
}
