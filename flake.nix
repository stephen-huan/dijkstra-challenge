{
  description = "dijkstra-challenge";

  inputs = {
    nixpkgs.follows = "maipkgs/nixpkgs";
    maipkgs.url = "github:stephen-huan/maipkgs";
  };

  outputs = { self, nixpkgs, maipkgs }:
    let
      inherit (nixpkgs) lib;
      systems = lib.systems.flakeExposed;
      eachDefaultSystem = f: builtins.foldl' lib.attrsets.recursiveUpdate { }
        (map f systems);
    in
    eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        inherit (maipkgs.legacyPackages.${system}) leanPackages;
        inherit (maipkgs.packages.${system}) nanoda;
        inputs = { inherit leanPackages nanoda; };
      in
      {
        packages.${system} = {
          even = pkgs.callPackage ./pkgs/1-even inputs;
          parity = pkgs.callPackage ./pkgs/2-parity inputs;
          mixed = pkgs.callPackage ./pkgs/3-parity inputs;
        };

        apps.${system}.default = {
          type = "app";
          program = lib.getExe (pkgs.writeShellApplication {
            name = "check";
            runtimeInputs = [ pkgs.bash ];
            text = ''
              systemd-run \
                --property=RestrictAddressFamilies=~AF_UNIX \
                --user \
                --pty \
                -E PATH="$PATH" \
                --working-directory "$(pwd)" \
                -- bash -c \
                  'lake env ${lib.getExe leanPackages.comparator} config.json'
            '';
          });
        };

        devShells.${system}.default = pkgs.mkShell {
          packages = [
            leanPackages.comparator
            # not necessarily the same as pkgs.lean4!
            leanPackages.lean4
            leanPackages.lean4export
            nanoda
            pkgs.landrun
          ];
        };
      }
    );
}
