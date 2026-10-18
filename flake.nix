{
  description = "Extreme value theory in Lean 4: development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        # `nix develop` gives elan (which installs the toolchain pinned in `lean-toolchain`),
        # plus the tools used by the scripts and the CI.
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            elan
            git
            curl
            python3
            gh
          ];
          shellHook = ''
            echo "Lean toolchain: $(cat lean-toolchain)"
            echo "Run 'lake exe cache get && lake build' to build the library."
          '';
        };

        formatter = pkgs.nixfmt-rfc-style;
      });
}
