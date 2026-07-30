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
          # imagemagick is only for `just render-review`; the render tests' own
          # browser and fonts come from tests/render/Dockerfile.
          buildInputs = with pkgs; [
            elan
            nodejs_24
            pnpm
            just
            imagemagick
          ];
        };
      });
    };
}
