{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    systems.url = "github:nix-systems/default";
  };

  outputs =
    {
      nixpkgs,
      systems,
      ...
    }:
    let
      inherit (nixpkgs) lib legacyPackages;
      eachPkgs = f: lib.genAttrs (import systems) (s: f (legacyPackages.${s}));
    in
    {
      devShells = eachPkgs (pkgs: {
        default = pkgs.mkShell {
          # elan provisions the Lean toolchain wrapped for NixOS;
          # node + pnpm are needed by `lake build` to bundle the widget JS.
          buildInputs = with pkgs; [
            elan
            nodejs_24
            pnpm
            just
          ];
        };
      });
    };
}
