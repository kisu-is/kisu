{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    crane.url = "github:ipetkov/crane";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{ self
    , flake-parts
    , rust-overlay
    , nixpkgs
    , crane
    , ...
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];

      perSystem =
        { pkgs, system, ... }:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ (import rust-overlay) ];
          };

          buildInputs = with pkgs; [ ];

          LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath buildInputs;

          devPackages = with pkgs; [
            (rust-bin.stable.latest.default.override {
              extensions = [
                "cargo"
                "clippy"
                "rust-src"
                "rust-analyzer"
                "rustc"
                "rustfmt"
              ];
            })
          ];

          craneLib = crane.mkLib pkgs;
        in
        {
          devShells = {
            default = pkgs.mkShell {
              inherit LD_LIBRARY_PATH buildInputs;
              packages = devPackages;
            };
          };

          packages = rec {
            mauve-cli = craneLib.buildPackage {
              src = craneLib.cleanCargoSource ./.;
              cargoBuildCommand = "cargo build --release -p mauve-cli";
              pname = "mauve-cli";
              inherit buildInputs;
            };

            default = mauve-cli;
          };

        };
    };
}
