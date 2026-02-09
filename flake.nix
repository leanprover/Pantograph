{
  description = "Pantograph";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };

  outputs = inputs @ {
    self,
    nixpkgs,
    flake-parts,
    lean4-nix,
    ...
  }:
    flake-parts.lib.mkFlake {inherit inputs;} {
      flake = {
      };
      systems = [
        "aarch64-linux"
        "aarch64-darwin"
        "x86_64-linux"
        "x86_64-darwin"
      ];
      perSystem = {
        system,
        pkgs,
        ...
      }: let
        manifest = pkgs.lib.importJSON ./lake-manifest.json;
        manifest-lspec = builtins.head manifest.packages;
        lean = lean4-nix.packages.${system}.lean-bin;
        lspecLib = lean.buildLeanPackage {
          name = "LSpec";
          roots = ["LSpec"];
          src = builtins.fetchGit {inherit (manifest-lspec) url rev;};
        };
        inherit (pkgs.lib.fileset) unions toSource fileFilter;
        src = ./.;
        set-project = unions [
          ./Pantograph.lean
          (fileFilter (file: file.hasExt "lean") ./Pantograph)
        ];
        set-test = unions [
          (fileFilter (file: file.hasExt "lean") ./Test)
        ];
        src-project = toSource {
          root = src;
          fileset = unions [
            set-project
          ];
        };
        src-repl = toSource {
          root = src;
          fileset = unions [
            set-project
            ./Main.lean
            ./Repl.lean
          ];
        };
        src-tomograph = toSource {
          root = src;
          fileset = unions [
            set-project
            ./Tomograph.lean
          ];
        };
        src-test = toSource {
          root = src;
          fileset = unions [
            set-project
            ./Repl.lean
            set-test
          ];
        };
        project = lean.buildLeanPackage {
          name = "Pantograph";
          roots = ["Pantograph"];
          src = src-project;
        };
        repl = lean.buildLeanPackage {
          name = "Repl";
          roots = ["Main" "Repl"];
          deps = [project];
          src = src-repl;
        };
        tomograph = lean.buildLeanPackage {
          name = "tomograph";
          roots = ["Tomograph"];
          deps = [project];
          src = src-tomograph;
        };
        test = lean.buildLeanPackage {
          name = "Test";
          # NOTE: The src directory must be ./. since that is where the import
          # root begins (e.g. `import Test.Environment` and not `import
          # Environment`) and thats where `lakefile.lean` resides.
          roots = ["Test.Main"];
          deps = [lspecLib repl];
          src = src-test;
        };
      in rec {
        packages = {
          inherit (project) sharedLib depRoots;
          inherit (repl) executable;
          tomograph = tomograph.executable;
          default = repl.executable;
        };
        legacyPackages = {
          inherit project;
        };
        checks = {
          test =
            pkgs.runCommand "test" {
              buildInputs = [test.executable lean.lean-all];
            } ''
              #export LEAN_SRC_PATH="${./.}"
              ${test.executable}/bin/test > $out
            '';
        };
        formatter = pkgs.alejandra;
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.prek
            lean.lean-all
          ];
        };
      };
    };
}
