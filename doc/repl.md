# REPL

This documentation is about interacting with the REPL.

## Examples

After building the `repl`, it will be available in `.lake/build/bin/repl`.
Execute it by either directly referring to its name, or `lake exe repl`.

``` sh
repl MODULES|LEAN_OPTIONS
```

The `repl` executable must be given with a list of modules to import. By default
it will import nothing, not even `Init`. It can also accept lean options of the
form `--key=value` e.g. `--pp.raw=true`.

After it emits the `ready.` signal, `repl` accepts commands as single-line JSON
inputs and outputs either an `Error:` (indicating malformed command) or a JSON
return value indicating the result of a command execution. The command must be
given in one of two formats

```
command { ... }
{ "cmd": command, "payload": ... }
```

The list of available commands can be found below. An empty command aborts the
REPL.

Example: (~5k symbols)
```
$ repl Init
env.catalog
env.inspect {"name": "Nat.le_add_left"}
```

Example with `mathlib4` (~90k symbols, may stack overflow, see troubleshooting)

```
$ repl Mathlib.Analysis.Seminorm
env.catalog
```

Example proving a theorem: (alternatively use `goal.start {"copyFrom": "Nat.add_comm"}`)
to prime the proof

```
$ repl Init
goal.start {"expr": "∀ (n m : Nat), n + m = m + n"}
goal.tactic {"stateId": 0, "tactic": "intro n m"}
goal.tactic {"stateId": 1, "tactic": "assumption"}
goal.delete {"stateIds": [0]}
stat {}
goal.tactic {"stateId": 1, "tactic": "rw [Nat.add_comm]"}
stat
```
where the application of `assumption` should lead to a failure.

For a list of commands, see [REPL Documentation](doc/repl.md).

### Project Environment

To use Pantograph in a project environment, setup the `LEAN_PATH` environment
variable so it contains the library path of lean libraries. The libraries must
be built in advance. For example, if `mathlib4` is stored at `../lib/mathlib4`,
the environment might be setup like this:

``` sh
LIB="../lib"
LIB_MATHLIB="$LIB/mathlib4/.lake"
export LEAN_PATH="$LIB_MATHLIB:$LIB_MATHLIB/aesop/build/lib:$LIB_MATHLIB/Qq/build/lib:$LIB_MATHLIB/std/build/lib"

LEAN_PATH=$LEAN_PATH repl $@
```
The `$LEAN_PATH` executable of any project can be extracted by
``` sh
lake env printenv LEAN_PATH
```

## Commands

See `Pantograph/Protocol.lean` for a description of the parameters and return values in JSON.
* `reset`: Delete all cached expressions and proof trees
* `stat`: Display resource usage
* `expr.echo {"expr": <expr>, "type": <optional expected type>, ["levels": [<levels>]]}`: Determine the
  type of an expression and format it.
* `env.catalog`: Display a list of all safe Lean symbols in the current environment
* `env.inspect {"name": <name>, "value": <bool>}`: Show the type and package of a
  given symbol; If value flag is set, the value is printed or hidden. By default
  only the values of definitions are printed.
* `env.save { "path": <fileName> }`, `env.load { "path": <fileName> }`: Save/Load the
  current environment to/from a file
* `env.module_read { "module": <name> }`: Reads a list of symbols from a module
* `env.describe {}`: Describes the imports and modules in the current environment
* `options.set { key: value, ... }`: Set one or more options. These are not Lean
  `CoreM` options; those have to be set via command line arguments.), for
  options see below.
* `options.print`: Display the current set of options
* `goal.start {["name": <name>], ["expr": <expr>], ["levels": [<levels>]], ["copyFrom": <symbol>]}`:
  Start a new proof from a given expression or symbol
* `goal.tactic {"stateId": <id>, ["goalId": <id>], ["autoResume": <bool>], ...}`:
  Execute a tactic string on a given goal site. The tactic is supplied as additional
  key-value pairs in one of the following formats:
  - `{ "tactic": <tactic> }`: Executes a tactic in the current mode
  - `{ "mode": <mode> }`: Enter a different tactic mode. The permitted values
    are `tactic` (default), `conv`, `calc`. In case of `calc`, each step must
    be of the form `lhs op rhs`. An `lhs` of `_` indicates that it should be set
    to the previous `rhs`.
  - `{ "expr": <expr> }`: Assign the given proof term to the current goal
  - `{ "have": <expr>, "binderName": <name> }`: Execute `have` and creates a branch goal
  - `{ "let": <expr>, "binderName": <name> }`: Execute `let` and creates a branch goal
  - `{ "draft": <expr> }`: Draft an expression with `sorry`s, turning them into
    goals. Coupling is not allowed.
  If the `goals` field does not exist, the tactic execution has failed. Read
  `messages` to find the reason.
* `goal.continue {"stateId": <id>, ["branch": <id>], ["goals": <names>]}`:
  Execute continuation/resumption
  - `{ "branch": <id> }`: Continue on branch state. The current state must have no goals.
  - `{ "goals": <names> }`: Resume the given goals
* `goal.remove {"stateIds": [<id>]}"`: Drop the goal states specified in the list
* `goal.print {"stateId": <id>}"`: Print a goal state
* `goal.save { "id": <id>, "path": <fileName> }`, `goal.load { "path": <fileName> }`:
  Save/Load a goal state to/from a file. The environment is not carried with the
  state. The user is responsible to ensure the sender/receiver instances share
  the same environment.
* `frontend.process { ["fileName": <fileName>,] ["file": <str>], readHeader: <bool>, inheritEnv: <bool>, invocations:
  <string>, sorrys: <bool>, typeErrorsAsGoals: <bool>, newConstants: <bool> }`:
  Executes the Lean frontend on a file, collecting the tactic invocations
  (`"invocations": output-path`), the sorrys and type errors into goal states
  (`"sorrys": true`), and new constants (`"newConstants": true`). In the case of
  `sorrys`, this command additionally outputs the position of each captured
  `sorry`. Conditionally inherit the environment from executing the file.
  Warning: Behaviour is unstable in case of multiple `sorry`s. Use the draft
  tactic if possible.

## Options

The full list of options can be found in `Pantograph/Protocol.lean`. Particularly:
- `automaticMode` (default on): Goals will not become dormant when this is
  turned on. By default it is turned on, with all goals automatically resuming.
  This makes Pantograph act like a gym, with no resumption necessary to manage
  your goals.
- `timeout` (default 0): Set `timeout` to a non-zero number to specify timeout
  (milliseconds) for all `CoreM` and frontend operations.

## Errors

When an error pertaining to the execution of a command happens, the returning JSON structure is

``` json
{ "error": "type", "desc": "description" }
```
Common error forms:
* `command`: Indicates malformed command structure which results from either
  invalid command or a malformed JSON structure that cannot be fed to an
  individual command.
* `index`: Indicates an invariant maintained by the output of one command and
  input of another is broken. For example, attempting to query a symbol not
  existing in the library or indexing into a non-existent proof state.

## Troubleshooting

If lean encounters stack overflow problems when printing catalog, execute this before running lean:
```sh
ulimit -s unlimited
```
