# Contributing

A Lean development shell is provided in the Nix flake. Nix usage is optional.

All commit messages must conform to the Conventional Commits specification.

## Testing

The tests are based on `LSpec`. To run tests, use either

``` sh
nix flake check
```
or
``` sh
lake test
```

You can run an individual test by specifying a prefix

``` sh
lake test -- Frontend/Collect
```


