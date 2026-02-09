# Contributing

A Lean development shell is provided in the Nix flake. Nix usage is optional.
Any contribution has to pass the pre-commit hooks, installable using either `prek` or `pre-commit`:
```sh
prek install
pre-commit install --install-hooks
```

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

## Formatting

When writing Lean code, follow the guidelines

- Functions should be in `camelCase`
- Theorems and tests should be in `snake_case`
- Write the `|` in a pattern-matching `let` on the next line. This is for visual
  distinction with long function arguments.
```lean
let .some result := function
  | fail "incorrect"
```
- Each test should be pinpointed and as devolatilized as possible.
