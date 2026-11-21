{
  description = "rulean: the tools that extract the verified core of rulean to Lean";

  # Aeneas pins the Charon commit that it needs, and Charon pins the Rust nightly that it needs. All other inputs follow these two, so one commit names the full extraction toolchain. con-ron uses the same Aeneas commit (spec 10.3).
  inputs = {
    aeneas.url = "github:AeneasVerif/aeneas/557eff83ecef5083b98a52a94ca7fae63d6c1dab";
    nixpkgs.follows = "aeneas/charon/nixpkgs";
    flake-utils.follows = "aeneas/flake-utils";
  };

  outputs = { nixpkgs, flake-utils, aeneas, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        charonPkgs = aeneas.inputs.charon.packages.${system};
        aeneasPkgs = aeneas.packages.${system};
      in {
        packages = {
          charon = charonPkgs.charon;
          aeneas = aeneasPkgs.aeneas;
          rustToolchain = charonPkgs.rustToolchain;
        };

        # The shell for `scripts/extract.sh`. It has the Rust nightly of Charon, not the stable toolchain of `rust-toolchain.toml`. Use it only for the extraction.
        devShells.default = pkgs.mkShell {
          packages = [
            charonPkgs.rustToolchain
            charonPkgs.charon
            aeneasPkgs.aeneas
          ];
        };
      });
}
