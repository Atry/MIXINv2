{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    nix-ml-ops = {
      url = "github:Atry/nix-ml-ops";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        systems.url = "github:nix-systems/default";
      };
    };
    # Required by devenv's `containers` feature, which looks up `inputs.nix2container` at the top level
    nix2container.follows = "nix-ml-ops/nix2container";
  };
  outputs = inputs: { };
}
