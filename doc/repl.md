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

Running repl with `--version` shows the version and then exits.

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
env.catalog {}
env.inspect {"name": "Nat.le_add_left"}
```

Example with `mathlib4` (~90k symbols, may stack overflow, see troubleshooting)

```
$ repl Mathlib.Analysis.Seminorm
env.catalog {}
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

Additional modules cannot be imported after the perennial process starts, either
via `env.load` or the frontend functions. The technical reason for this is when
Lean cannot determine whether an imported module's initializer has run.

## Commands

See `Pantograph/Protocol.lean` for a description of the parameters and return values in JSON.
* `reset`: Delete all cached expressions and proof trees
* `stat`: Display resource usage
* `options.set { key: value, ... }`: Set one or more options. These are not Lean
  `CoreM` options; those have to be set via command line arguments.), for
  options see below.
* `options.print`: Display the current set of options
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
* `env.parse { "input": <input>, "category": <parser-category> }`: Parse a bit
  of syntax and returns the parser's terminal position.
* `goal.start {["name": <name>], ["expr": <expr>], ["levels": [<levels>]], ["copyFrom": <symbol>]}`:
  Start a new proof from a given expression or symbol
* `goal.tactic {"stateId": <id>, ["goalId": <id>], ["autoResume": <bool>], ...}`:
  Execute a tactic string on a given goal site. The tactic is supplied as additional
  key-value pairs in one of the following formats:
  - `{ "tactic": <tactic> }`: Executes a tactic or a sequence of tactics in the
    current mode.
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
* `goal.subsume {"stateId": <id>, "goal": <name>, "candidates":
  <names>, ["srcStateId": <id>]}`: determine if any goal in `candidates` (coming
  from either the provided state id or `srcStateId`) subsumes `goal`. It returns
  the *subsumptor* (goal providing the solution) and a new state id if the
  subsumption is not a cycle, in which case the *subsumend* `goal` is erased.
* `goal.remove {"stateIds": [<id>]}"`: Drop the goal states specified in the list
* `goal.print {"stateId": <id>}"`: Print a goal state
* `goal.save { "id": <id>, "path": <fileName> }`, `goal.load { "path": <fileName> }`:
  Save/Load a goal state to/from a file. The environment is not carried with the
  state. The user is responsible to ensure the sender/receiver instances share
  the same environment.
* `frontend.process { ["fileName": <fileName>,] ["file": <str>], readHeader:
  <bool>, inheritEnv: <bool>, invocations: <string>, newConstants: <bool> }`:
  Executes the Lean frontend on a file, collecting the tactic invocations
  (`"invocations": output-path`), or new constants (`newConstants`)
* `frontend.distil { "file": <str>, ["binderName": <str>], "ignoreValues": bool
  }`: Extract condensed search targets from a file, where coupled search targets
  will be condensed into one. Set `binderName` to override the binder name to
  e.g. `f`. Set `ignoreValues` to false to incorporate existing solutions.

  Note that `example`s are not search targets!
* `frontend.track { "src": <str>, "dst": <str> }`: Check if one file conforms to
  another. The declarations in `src` could have `sorry`s and the declarations in
  `dst` would fill them.
* [Experimental] `frontend.refactor { "file": <str>, "coreOptions":
  [["<key>=<val>"]] }`: Group dependent `sorry`s into one single `sorry`.
  Currently only flat dependencies are supported (i.e.  an object with a list of
  properties).

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
* `parse`: Indicates parsing errors
* `elab`: Indicates elaboration errors
* `frontend`: Indicates whole-file parsing and elaboration errors
* `io`: Generic IO error
* `command`: The command's argument is malformed

## Troubleshooting

If lean encounters stack overflow problems when printing catalog, execute this before running lean:
```sh
ulimit -s unlimited
```
