with (import <nixpkgs> {});

stdenv.mkDerivation {
  name = "idris-benchmarksgame-nbody";
  src = ./.;
  buildInputs = [ gmp haskellPackages.idris ];
}
