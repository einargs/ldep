{ pkgs ? (import <nixpkgs> {}) }:

let inherit (pkgs) stdenv fetchFromGitHub z3 ocamlPackages makeWrapper; in

pkgs.mkShell {
  nativeBuildInputs = [ makeWrapper ];

  buildInputs = with ocamlPackages; [
    z3 ocaml findlib batteries menhir stdint
    zarith camlp4 yojson pprint
    ulex ocaml-migrate-parsetree process ppx_deriving ppx_deriving_yojson ocamlbuild
  ];

  /*makeFlags = [ "PREFIX=$(out)" ];

  preBuild = ''
    patchShebangs src/tools
    patchShebangs bin
  '';
  buildFlags = "-C src/ocaml-output";

  preInstall = ''
    mkdir -p $out/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib/fstarlib
  '';
  installFlags = "-C src/ocaml-output";
  postInstall = ''
    wrapProgram $out/bin/fstar.exe --prefix PATH ":" "${z3}/bin"
  '';

  meta = with stdenv.lib; {
    description = "ML-like functional programming language aimed at program verification";
    homepage = https://www.fstar-lang.org;
    license = licenses.asl20;
    platforms = with platforms; darwin ++ linux;
    maintainers = with maintainers; [ gebner ];
  };*/
}
