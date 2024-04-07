with (import <nixpkgs> {});
let haskell810 = haskell.packages.ghc962;
in mkShell {
  nativeBuildInputs = [
    pkg-config
    haskell810.haskell-language-server
    # haskell.compiler.ghc926
    haskell.compiler.native-bignum.ghc962
    cabal-install
  ];

  buildInputs = [
    zlib
    libsodium
    secp256k1
  ];

  shellHook = ''
    export LC_ALL=C.utf8
  '';
}
