{ pkgs ? (import <nixpkgs> {}) }:

pkgs.stdenv.mkDerivation {
  name = "sys";
  buildInputs = [ (pkgs.haskellPackages.ghcWithPackages (p: with p; [ free text tardis comonad unordered-containers ]))  ];
}
