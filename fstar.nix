{ stdenv, fetchFromGitHub, z3, ocamlPackages, makeWrapper, which, file }:

stdenv.mkDerivation rec {
  name = "fstar-${version}";
  version = "commit-1aeb400"; 
  src = fetchFromGitHub {
    owner = "FStarLang";
    repo = "FStar";
    rev = "d510234e841715b5ba4debd2aa7214954e084a07";
    sha256 = "12iwih61pksjskn5kdb6srb9v3v38wq7kz6dw5xnbgwb2vyi66fm";
  };

  nativeBuildInputs = [ makeWrapper ];

  buildInputs = with ocamlPackages; [
    file which
    z3 ocaml findlib batteries menhir stdint
    zarith camlp4 yojson pprint
    ulex ocaml-migrate-parsetree process ppx_deriving ppx_deriving_yojson ocamlbuild
  ];

  makeFlags = [ "PREFIX=$(out)" ];

  preBuild = ''
    echo "OUT IS"
    echo $out
    patchShebangs src/tools
    patchShebangs bin
  '';
  buildFlags = "-C src -j6 ocaml-fstar-ocaml";

  /*installPhase = ''
    mkdir -p $out/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib/fstarlib
    make -C src/ocaml-output -j6
    make -C src -j6
    wrapProgram $out/bin/fstar.exe --prefix PATH ":" "${z3}/bin"
  '';*/
  installPhase = ''
    make -C ulib install-fstarlib install-fstar-tactics
    mkdir -p $out/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib/fstarlib
    # mkdir -p $out/bin/
    # cp bin/fstar.exe $out/bin/fstar.exe
    ls bin/
    make -C src/ocaml-output install PREFIX=$out
    ls bin/
    ls $out/bin/
    wrapProgram $out/bin/fstar.exe --prefix PATH ":" "${z3}/bin"
  '';
  /*preInstall = ''
    mkdir -p $out/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib/fstarlib
  '';
  #installFlags = "-C src -j6 ocaml-fstar-ocaml";
  postInstall = ''
    wrapProgram $out/bin/fstar.exe --prefix PATH ":" "${z3}/bin"
  '';*/

  meta = with stdenv.lib; {
    description = "ML-like functional programming language aimed at program verification";
    homepage = https://www.fstar-lang.org;
    license = licenses.asl20;
    platforms = with platforms; darwin ++ linux;
    maintainers = with maintainers; [ gebner ];
  };
}
